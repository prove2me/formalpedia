-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_behrend_margin_parameters
-- name    : MME.StothersFourth.mme_stothers_fixed_behrend_margin_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:21:13.590075+00:00
-- url     : https://prove2.me/theorems/0ca28e17-441f-4f87-9e0b-8df0f585c38e
-- title:
--   Prime and progression-free parameters for the fixed Stothers hash
-- statement:
--   Let D* be a positive target-star degree and put D = (6(N+1))^100 D*. Assume D ≤ 5^(1000N). Then there are an odd prime p ≥ 9 and a three-term-progression-free set S contained in {0,…,⌊p/2⌋-1} such that p^2 exp(-10^6 √(N+1)) + 3D*D ≤ D*|S|. These parameters supply the quantitative surplus required by the fixed affine-hash selection theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The prime and progression-free-set existence is supplied by the reusable Prove2Me Behrend theorem.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_hash_collision_margin

open MME BigOperators Filter Topology

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_behrend_margin_parameters
    (N Dstar : ℕ) (hDstar : 1 ≤ Dstar)
    (hD5 :
      (6 * (N + 1)) ^ 100 * Dstar ≤ 5 ^ (1000 * N)) :
    let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
    ∃ p : ℕ, p.Prime ∧ 9 ≤ p ∧ Odd p ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (p : ℝ) ^ 2 *
              Real.exp
                (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))) +
            3 * (Dstar : ℝ) * (D : ℝ) ≤
          (Dstar : ℝ) * (S.card : ℝ) := by
  sorry
