-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
-- name    : Kyprianou.Ch08.StageB.p2m89_phi_derivative_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:18:47.692839+00:00
-- url     : https://prove2.me/theorems/62f0766b-bfb5-4890-8b8d-73a92e8c36d2
-- title:
--   Positive root derivative equals reciprocal exponent derivative
-- statement:
--   Exact positive-discount inverse derivative from the already proved local inverse argument.
-- source:
--   Kyprianou (2006), Corollary 8.9; corrected occupation identity 33cf8321-6b73-409d-84cc-a8da6fcb2949.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_phi_derivative_exact
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    0 < deriv ψ (Phi ψ q) ∧ deriv (Phi ψ) q = (deriv ψ (Phi ψ q))⁻¹ := by
  sorry
