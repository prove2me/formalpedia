-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2_operational_core
-- name    : ITPIRPreproc.MatchVec.lemma_4_2_operational_core
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:22.444142+00:00
-- url     : https://prove2.me/theorems/c8ca1655-877a-4f56-b163-8e0a2b517ed0
-- title:
--   Lemma 4.2 — word-RAM construction, conditional round interfaces, and costs
-- statement:
--   This is the operational core of Lemma 4.2. Starting from an implemented one-compatible-hint primitive, construct the five **uniform word-RAM programs** of the compiler in §4.2 and prove that the resulting scheme is well formed. For every valid $m\ge8$, every instance and every $\lambda\ge1$, the construction must additionally establish:
--
--   * the per-index conditional uniform-query interface `IndexUniformStep`, expressing the invariant that every current key and every query is uniform on its required key space, including across epoch boundaries and for cache-only rounds;
--   * an `IndependentPoolFailure` model for every positive-probability query prefix, with $s=8(\lambda+1)$ pool-failure events, each of conditional probability at most $7/8$, and with decoding failure contained in their intersection;
--   * the stated worst-case communication, space and work bounds for an absolute constant $C$.
--
--   The intended program construction is exactly §4.2: preprocessing independently refreshes all keys in two banks, saves the streaming hint values, and initializes the cache; an epoch replaces the current bank by the next one and samples a new next bank; each noncached target makes one attempt per pool, scanning in order for the first key containing the target; cached targets use independent dummy queries; reconstruction keeps only a successful attempt whose output bit is supported by the saved hint. The offline answer is the $m$ new keys. No shortcut at activation secrets is permitted.
--
--   The cache is still required here, even though it affects costs rather than the proof of the information-theoretic error exponent. In particular, all worst-case RAM space charges include the full client state as well as quantification over reachable states.
--
--   **Formalization Note** The final adaptive factorization `StepPrivate` and the per-round probability bound are deliberately not assumptions of this theorem: they are obtained from the two interfaces by separate probability transfer lemmas. This child therefore contains program construction, the fundamental conditional invariants, and cost accounting, not the whole Lemma 4.2.
-- source:
--   Dujmovic--Lai--Wichs, STOC 2027 submission #572, Lemma 4.2 and its proof in §4.2, printed pp.12--15 (PDF pp.14--17). In particular printed p.14 (construction and efficiency), p.14 correctness (sound reconstruction and unsuccessful pool attempts), and p.15 privacy (conditional uniformity across rounds and epochs).

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerRoundModels
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency

open scoped ENNReal

open ITPIRPreproc.MatchVec
open ITPIRPreproc.MatchVec.WordRAM

theorem ITPIRPreproc.MatchVec.lemma_4_2_operational_core :
    ∃ C : ℝ, ∀ (P : ∀ m : ℕ, OCHP (m * m)) (I : OCHPImpl P),
      ∃ S : Scheme, S.WellFormed ∧
        ∀ (m : ℕ) (tB tS tQ tD tA : ℝ) (qLen aLen : ℕ), 8 ≤ m →
          (P m).IsOneCompatibleHint m → I.Efficient m tB tS tQ tD tA qLen aLen →
          ∀ lam : ℕ, 1 ≤ lam →
            IndexUniformStep S (m * m) lam ∧
            FailureModeled S (m * m) lam (8 * (lam + 1)) ∧
            MeetsBudget S (m * m) lam
              { preWork := C * (lam * m * tB + lam * (m * m) * tS)
                preSpace := C * (tB + lam * m * tS)
                online := C * (lam * (qLen + aLen) + Real.log (m * m))
                offline := C * m
                clientWork := C * (lam * m * (tB + tS) + lam * (tQ + tD) + m * Real.log (m * m))
                clientSpace := C * (lam * m * (tB + tS) + lam * (tQ + tD) + m * Real.log (m * m))
                serverWork := C * (lam * tA + m) } := by sorry
