-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
-- name    : Kyprianou.Ch08.StageB.original_unrestricted_upcrossing_discount_bound_zero_included
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:12:38.723811+00:00
-- url     : https://prove2.me/theorems/de42f26a-9b94-4308-b486-d5c8d4969c8a
-- title:
--   Original spectrally negative Lévy upcrossing discount integrability and Laplace-root cap including zero discount
-- statement:
--   For the original Kyprianou spectrally negative process and every nonnegative discount, the first strict upcrossing discounted payoff is integrable and its expectation is bounded by the exponential of the negative largest nonnegative Laplace root, including the zero-discount case. This is a genuine source mathematical prerequisite of the unit cap of the original no-drawdown excursion survival transform.
-- source:
--   Exact original D.X passage component factored from the verified proof architecture for Kyprianou.Ch08.StageB.actual_height_tail_unit_cap_independent. Reuse Proved public Avram q>=0 root bound 12fbdda4-765b-4ae6-a0e6-6f8a30895236 and the Proved original-to-filtered Avram model coupling 297b1fce-72b0-452b-a84f-3c5e7a59fe1e.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.original_unrestricted_upcrossing_discount_bound_zero_included
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun ω => discountedAt q (tauPlus D.X 1 ω)) P ∧
    (∫ ω, discountedAt q (tauPlus D.X 1 ω) ∂P) ≤
      Real.exp (-(Phi ψ q * 1)) := by
  sorry
