-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_4_4
-- name    : NoPerfectRandComp.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:53.938184+00:00
-- url     : https://prove2.me/theorems/94d0b9e4-94ab-4899-9412-3f18d512191a
-- title:
--   Lemma 4.4 — an explicit hard distribution for the core, $\mathrm{R}(S_q)>u_q^2q^3$
-- statement:
--   Let $q \ge 4$. There is a distribution $\mu_q$ supported on the domain of the core $S_q$ such that every deterministic decision tree of depth at most
--   $$
--   R_0 = u_q^2 q^3
--   $$
--   computes $S_q$ with success probability at most $5/8$ under $\mu_q$. In particular
--   $$
--   \mathrm{R}(S_q) > u_q^2 q^3 .
--   $$
--
--   The distribution feeds the list direct-product bound (Lemma 4.6) in the lower bound for the outer function.
--
--   Differences from the source:
--   - encoding: "success probability at most 5/8, and hence at most 2/3" → only the 5/8 bound, as the μ_q-mass of the inputs on which the tree outputs S_q(x); reason: 5/8 < 2/3, so the second clause is implied
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 4.4, p.13 (standing assumption "Fix q ≥ 4", §4.1, p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_core
import Definitions.Def_NoPerfectRandComp_rq
import Definitions.Def_NoPerfectRandComp_uq

namespace NoPerfectRandComp

/-- Lemma 4.4 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.13 (an explicit hard distribution for the core): for `q ≥ 4` there is
a distribution `μ_q` supported on the domain of `S_q` such that every ordinary-query tree of depth
at most `R₀ = u_q² q³` has success probability at most `5/8` under `μ_q`; in particular
`R(S_q) > u_q² q³`.

**Formalization Note** `S_q = core k_q r_q u_q`. A tree of depth at most `R₀` makes at most `R₀`
queries on every input. The success probability is the `μ_q`-mass (in `ℝ≥0∞`) of the inputs on
which the tree outputs `S_q(x)`. The page's "and hence at most 2/3" follows from `5/8 ≤ 2/3`. -/
theorem lemma_4_4 (q : ℕ) (hq : 4 ≤ q) :
    ∃ μ : PMF (Fin (uq q) × Fin (uq q) × SeedIdx (kq q) → Bool),
      (∀ x ∈ μ.support, x ∈ (core (kq q) (rq q) (uq q)).dom) ∧
      (∀ T : QAlgorithms.DecisionTree (Fin (uq q) × Fin (uq q) × SeedIdx (kq q)) Bool Bool,
        T.MakesAtMost (uq q ^ 2 * q ^ 3) →
        μ.toOuterMeasure {x | T.eval x = (core (kq q) (rq q) (uq q)).val x} ≤ 5 / 8) ∧
      uq q ^ 2 * q ^ 3 < R (core (kq q) (rq q) (uq q)) := by sorry

end NoPerfectRandComp
