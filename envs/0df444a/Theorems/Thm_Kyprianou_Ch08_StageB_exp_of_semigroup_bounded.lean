-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_exp_of_semigroup_bounded
-- name    : Kyprianou.Ch08.StageB.exp_of_semigroup_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:35:56.800778+00:00
-- url     : https://prove2.me/theorems/2a006b93-0e73-4775-9e2e-d831183699ec
-- title:
--   Cauchy exponential lemma: bounded positive semigroup on positives is exponential
-- statement:
--   A positive multiplicative semigroup on the positive reals that is bounded above on [1,2] is exponential: f(a) = exp(a * log f(1)). Pure Cauchy analysis isolating the regularity-to-exponential step of the T3 actual-height multiplicative law.
-- source:
--   Source-faithful analysis child of Kyprianou Chapter 8 Theorem 8.2 actual-height multiplicative law (parent 027be585-204d-4aae-93f8-d5329c6a8b14): isolates the pure Cauchy regularity-to-exponential step. The parent T3 follows from the fixed-height semigroup law plus sibling tail-bounds positivity (T1 7b9a2094), boundedness, and this lemma.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.exp_of_semigroup_bounded
    (f : ℝ → ℝ)
    (hsemi : ∀ x y : ℝ, 0 < x → 0 < y → f (x + y) = f x * f y)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hbdd : ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ 2 → f x ≤ B) :
    ∀ a : ℝ, 0 < a → f a = Real.exp (-a * (-Real.log (f 1))) := by
  sorry
