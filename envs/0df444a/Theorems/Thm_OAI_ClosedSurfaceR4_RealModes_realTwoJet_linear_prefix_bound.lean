-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_RealModes_realTwoJet_linear_prefix_bound
-- name    : OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:37:49.501201+00:00
-- url     : https://prove2.me/theorems/aef7ef4d-0659-4cbe-844f-35dd612ae407
-- title:
--   OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/LinearFrameJetBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/LinearFrameJetBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.RealModes`, with `open Set`, `open scoped ContDiff`, `open SmallModes WeightedEstimates`):
--
--   ```lean
--   theorem realTwoJet_linear_prefix_bound {U : Set Base} (hU : IsOpen U)
--       {F : RField 4} (hF : ContDiff ℝ ∞ F) {s C D : ℝ} {m : ℕ}
--       (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
--       (L : Base ≃L[ℝ] Base) (hD : 1 ≤ D) (hL : ‖L.toContinuousLinearMap‖ ≤ D)
--       (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) F) :
--       WeightedBound (L ⁻¹' U) s m (C*D^(m+2)) (realTwoJet (F ∘ L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.RealModes.realTwoJet` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver` and `OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/LinearFrameJetBound.lean (declaration OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4

namespace RealModes
open SmallModes WeightedEstimates

theorem realTwoJet_linear_prefix_bound {U : Set Base} (hU : IsOpen U)
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (L : Base ≃L[ℝ] Base) (hD : 1 ≤ D) (hL : ‖L.toContinuousLinearMap‖ ≤ D)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) F) :
    WeightedBound (L ⁻¹' U) s m (C*D^(m+2)) (realTwoJet (F ∘ L)) := by
  sorry

end RealModes
end ClosedSurfaceR4

end

end OAI
end
