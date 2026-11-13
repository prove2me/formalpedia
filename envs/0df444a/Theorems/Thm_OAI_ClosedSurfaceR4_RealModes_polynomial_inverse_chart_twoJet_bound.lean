-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_RealModes_polynomial_inverse_chart_twoJet_bound
-- name    : OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:59:07.323061+00:00
-- url     : https://prove2.me/theorems/54361884-0559-498f-9031-9cfc943f679c
-- title:
--   OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseChartJetTransfer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseChartJetTransfer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.RealModes`, with `open Set`, `open scoped ContDiff`, `open SmallModes WeightedEstimates PhaseGeometry`):
--
--   ```lean
--   theorem polynomial_inverse_chart_twoJet_bound (m : ℕ) :
--       ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
--       ∀ (F : RField 4) (e : OpenPartialHomeomorph Base Base),
--         ContDiff ℝ ∞ F → ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
--       ∀ s B : ℝ, 0 < s → s ≤ 1 → 1 ≤ B →
--         (∀ j ≤ m+2, WeightedBound e.source 1 j (B/s^(j-2)) F) →
--         (∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ e.source,
--           ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
--         (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
--         WeightedBound e.target s m (C*B^d) (realTwoJet (F ∘ e.symm))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.RealModes.realTwoJet` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.coordDet` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver` and `OAI_ClosedSurfaceR4_RealModes_polynomial_nonlinear_phase_frame_bound` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseChartJetTransfer.lean (declaration OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates PhaseGeometry

theorem polynomial_inverse_chart_twoJet_bound (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (F : RField 4) (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
    ∀ s B : ℝ, 0 < s → s ≤ 1 → 1 ≤ B →
      (∀ j ≤ m+2, WeightedBound e.source 1 j (B/s^(j-2)) F) →
      (∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      WeightedBound e.target s m (C*B^d) (realTwoJet (F ∘ e.symm)) := by
  sorry

end ClosedSurfaceR4.RealModes

end

end OAI
end
