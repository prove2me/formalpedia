-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_real_finset_weighted_square_integrable
-- name    : Kyprianou.ProofPreparation.real_finset_weighted_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:10:27.838593+00:00
-- url     : https://prove2.me/theorems/50148d51-05ac-4fe3-b10d-2737c1ffb080
-- title:
--   Integrability of squared finite weighted sums from pairwise product integrability
-- statement:
--   If all pairwise products of a finite family of real functions are Bochner integrable under a measure, then the square of every finite real weighted sum is Bochner integrable. Derived by expanding the finite square into a double sum, applying integrable_finset_sum and scalar multiplication. Supports centred finite-simple Poisson stochastic integral L² isometry.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, deterministic finite-simple L² integrability step.

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem real_finset_weighted_square_integrable
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (F : Finset ι) (X : ι → Ω → ℝ)
    (a : ι → ℝ)
    (hprod : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => X i ω * X j ω) P) :
    Integrable (fun ω => (∑ i ∈ F, a i * X i ω) ^ 2) P := by sorry
end Kyprianou.ProofPreparation
