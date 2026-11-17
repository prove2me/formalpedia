-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_7_3
-- name    : KAQROM.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:57:16.974585+00:00
-- url     : https://prove2.me/theorems/cedc02f7-45cd-4b20-b9ad-c5a37d69b746
-- title:
--   Theorem 7.3 — lifting: a $q_D$-query quantum distinguisher of two classical-query samplers becomes a classical one with $\lceil q_S/\delta^2\rceil$ queries, losing at most $2\delta+4q_D\sqrt\delta$
-- statement:
--   Let $S_0,S_1$ be samplers that each make at most $q_S$ classical queries to $H\leftarrow\mathcal H$ and output a classical string in the same finite sample space; their local computation may be quantum. For a distinguisher $D$ on the sampled string let
--   $$
--   \mathrm{Adv}^{\mathrm{dist}}_{S_0,S_1,D}=\bigl|\Pr[D^H(S_1^H)=1]-\Pr[D^H(S_0^H)=1]\bigr|,
--   $$
--   each probability sampling a uniform $H$ and independent private randomness for sampler and distinguisher.
--
--   1. If $D$ makes at most $q_D$ quantum queries, then for every $0<\delta<1$ there is a computationally unbounded classical distinguisher $C_\delta$ making at most $\lceil q_S/\delta^2\rceil$ classical queries with
--   $$
--   \mathrm{Adv}^{\mathrm{dist}}_{S_0,S_1,C_\delta}\ \ge\ \mathrm{Adv}^{\mathrm{dist}}_{S_0,S_1,D}-2\delta-4q_D\sqrt\delta .
--   $$
--   2. Consequently there is an absolute constant $C>0$ such that for every $0<\varepsilon<1$ the additive loss can be made at most $\varepsilon$ by a classical distinguisher making at most $C\bigl(q_S\max\{1,q_D\}^4/\varepsilon^4+1\bigr)$ queries.
--
--   Quantum queries therefore give no advantage in distinguishing two distributions that are sampled with classical queries, up to a polynomial increase in the query count.
--
--   Differences from the source:
--   - encoding: security parameter λ and inputs 1^λ → one fixed λ; 1^λ arguments dropped; reason: the quantitative statement is per λ
--   - generalization: X = {0,1}^{n(λ)}, Y = {0,1}^{ℓ(λ)} with n, ℓ polynomially bounded → X any finite type, Y = Fin ℓ → ZMod 2 for any ℓ (XOR is +); reason: no bound depends on n or ℓ; the statement specializes to X = {0,1}^n
--   - encoding: quantum oracle algorithm with at most q queries → exactly q query rounds interleaved with arbitrary channels (published KAQROM.QAlg); reason: a query on the response state |+⟩^ℓ acts as the identity, so idle queries pad; parties are computationally unbounded
--   - encoding: classical oracle access → query steps whose instruments are selected by the classical record (CStage / published KAQROM.PrefixParty); reason: queries and answers are classical, the residual state stays quantum; this is Definition 3.1's notion
--   - encoding: all-zero private registers, local state preparation and private randomness inside the algorithms → arbitrary oracle-independent initial density operators; reason: local preparation from the all-zero state gives exactly these
--   - encoding: a computationally unbounded classical distinguisher → RandDet: finitely many coin values, deterministic classical-query algorithms, worst-case query bound over coins, oracles and inputs; reason: finitely many coins make the existence claim stronger
--   - reading: O(q_S max{1,q_D}⁴/ε⁴ + 1) → one absolute constant C > 0, quantified before the sample space, samplers, distinguisher and ε, times the printed expression; reason: the proof supplies it through δ = (ε/(8 max{1,q_D}))²
--   - generalization: worst-case query bound over every branch → bound required only on branches of positive probability; reason: zero-probability branches change no probability; the paper's bound implies the hypothesis
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.3, p.74

import Mathlib
import Definitions.Def_KAQROM_Supplement_DetAttacker
import Definitions.Def_KAQROM_Supplement_Sampler

namespace KAQROM.Supplement

open KAQROM

/-- **Theorem 7.3 (Lifting for two classical-query samplers).** Let `S₀, S₁` be samplers that each
make at most `q_S` classical queries to `H ← ℋ` and output a classical string in the same finite
sample space (their local computation may be quantum). If `D` makes at most `q_D` quantum queries,
then for every `0 < δ < 1` there is a computationally unbounded classical distinguisher `C_δ`
making at most `⌈q_S/δ²⌉` classical queries with
`Adv^{dist}_{S₀,S₁,C_δ} ≥ Adv^{dist}_{S₀,S₁,D} − 2δ − 4q_D√δ`. Consequently, for every
`0 < ε < 1` the additive loss can be made at most `ε` with a classical query bound of
`O(q_S max{1, q_D}⁴/ε⁴ + 1)`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.3, p.74.

**Formalization Note.** A classical distinguisher is a randomized classical-query algorithm on the
sample (`RandDet`, finitely many coin values), its query bound worst case over coins, oracles and
inputs. The `O(·)` is one absolute constant `C > 0` quantified before the sample space, the
samplers, the distinguisher and `ε`. -/
theorem theorem_7_3 :
    (∀ {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Z : Type} [Fintype Z]
      (S0 S1 : Sampler X ℓ Z) (qS : ℕ), S0.QueriesLe qS → S1.QueriesLe qS →
      ∀ (D : QDist X ℓ Z) (δ : ℝ), 0 < δ → δ < 1 →
        ∃ Cδ : RandDet Z X ℓ Bool, Cδ.QueriesLe ⌈(qS : ℝ) / δ ^ 2⌉₊ ∧
          advDist S0 S1 D.prob - 2 * δ - 4 * (D.q : ℝ) * Real.sqrt δ ≤
            advDist S0 S1 (fun H z => Cδ.prob H z true)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Z : Type} [Fintype Z]
        (S0 S1 : Sampler X ℓ Z) (qS : ℕ), S0.QueriesLe qS → S1.QueriesLe qS →
        ∀ (D : QDist X ℓ Z) (ε : ℝ), 0 < ε → ε < 1 →
          ∃ (Cε : RandDet Z X ℓ Bool) (N : ℕ), Cε.QueriesLe N ∧
            (N : ℝ) ≤ C * ((qS : ℝ) * ((max 1 D.q : ℕ) : ℝ) ^ 4 / ε ^ 4 + 1) ∧
            advDist S0 S1 D.prob - ε ≤ advDist S0 S1 (fun H z => Cε.prob H z true)) := by sorry

end KAQROM.Supplement
