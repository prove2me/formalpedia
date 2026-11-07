-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_10
-- name    : NoPerfectRandComp.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:28.43275+00:00
-- url     : https://prove2.me/theorems/c901335c-ddbc-4d56-b2fb-d7bb960fae12
-- title:
--   Lemma 5.10 — the composed seed $p_q\circ\hat M_q$ at error $1/(100q^2)$ and cost $B_q$
-- statement:
--   Let $q \ge 3$ be odd. The partial composition $p_q \circ \hat M_q$ has a randomized algorithm with error at most $1/(100q^2)$ on every valid input and worst-case cost
--   $$
--   B_q = k_q (6q+2)\hat C_q + q^3 \hat C_q ;
--   $$
--   the cost bound holds also on every input outside the promise.
--
--   It is the building block of the core algorithm of the upper bound (29).
--
--   Differences from the source:
--   - generalization: q = 2^s − 1 (the standing choice of §5; the seed is introduced under "Fix q ≥ 4") → every odd q ≥ 3; reason: the proof uses Lemma 5.3 (valid for odd q ≥ 3) and a Chebyshev bound valid for every q, and 2^s − 1 is odd and at least 3 for s ≥ 2
--   - generalization: the paper's fixed pointer-cell encoding → every admissible encoding; reason: the proof runs Lemma 5.3 and reads inner inputs in full
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.10 and Eq. (27), p.24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_seed
import Definitions.Def_NoPerfectRandComp_Mhat
import Definitions.Def_NoPerfectRandComp_kq
import Definitions.Def_NoPerfectRandComp_rq
import Definitions.Def_NoPerfectRandComp_Bq__ccb8cb

namespace NoPerfectRandComp

/-- Lemma 5.10 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), pp.24–25: the partial composition `p_q ∘ M̂_q` has an algorithm with
error at most `1/(100 q²)` on valid inputs and worst-case cost
`B_q = k_q (6q + 2) Ĉ_q + q³ Ĉ_q` ((27)); the cost bound holds also on every input outside its
promise.

**Formalization Note** Stated for every odd `q ≥ 3` (the paper's `q = 2ˢ − 1`, where Lemma 5.3
applies) and every admissible encoding. `p_q = seed k_q r_q`; the inner function is total, so the
domain of the composition is the set of inputs whose vector of `M̂_q`-values lies in the seed's
domain. -/
theorem lemma_5_10 (q : ℕ) (hq : Odd q) (hq3 : 3 ≤ q) (enc : Encoding (bq q) (PtrCell q)) :
    ∃ A : QAlgorithms.RandDecisionTree
        (SeedIdx (kq q) × (Fin q × (Fin q × Fin q × Fin (Chat q)))) Bool Bool,
      QAlgorithms.RandMakesAtMost A (Bq q) ∧
      ∀ x ∈ ((seed (kq q) (rq q)).comp (PartialFn.total (Mhat q enc))).dom,
        QAlgorithms.successProb A x
            (!((seed (kq q) (rq q)).comp (PartialFn.total (Mhat q enc))).val x) ≤
          1 / (100 * (q : ℝ) ^ 2) := by sorry

end NoPerfectRandComp
