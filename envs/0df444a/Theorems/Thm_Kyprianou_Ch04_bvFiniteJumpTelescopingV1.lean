-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTelescopingV1
-- name    : Kyprianou.Ch04.bvFiniteJumpTelescopingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:13:09.109465+00:00
-- url     : https://prove2.me/theorems/d991b29d-baa6-4426-a0d5-e69864473dcb
-- title:
--   Finite-jump chain rule with a combined directional derivative
-- statement:
--   Induct over the largest retained time and telescope the affine integral and jump increment ledgers. The empty case is the affine fundamental theorem.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteJumpTelescopingV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      f (T,P S T) = f (0,a) +
        (∫ u in 0..T, fderiv ℝ f (u,P S u) (1,d)) +
        ∑ s ∈ S, (f (τ s,P S (τ s)) - f (τ s,Q S (τ s))) := by
  sorry
