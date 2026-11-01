-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_QuaternionFrame_arrayCoupledIntegrand_le_reduced
-- name    : OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:48:42.856317+00:00
-- url     : https://prove2.me/theorems/0a91d50b-6732-4020-97a5-35f21d63e19f
-- title:
--   OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced` of [lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.QuaternionFrame`, with `open scoped BigOperators`, `open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry`, `open Energy QuarticEnergy Quadratic Potential Boundary`):
--
--   ```lean
--   theorem arrayCoupledIntegrand_le_reduced
--       (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
--       (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
--       (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
--       (hZb : ∀ r i, gradientDivergence Z r i = 0)
--       (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
--       (hVb : ∀ r i, gradientDivergence V r i = 0)
--       (hzero : normalizedBlockNorm A = 0 → Z = 0)
--       (hzerob : normalizedBlockNorm U = 0 → V = 0)
--       (D : PointwiseSpectrum A U Z p) (F : PointwiseSpectrum U A V q)
--       (hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2)
--       (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
--         ‖p - q‖ ^ 2)
--       (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
--         ‖p - q‖ ^ 2) :
--       arrayCoupledIntegrand A U Z V a ab p q ≤
--         reducedIntegrand (normalizedBlockNorm A) (normalizedBlockNorm U) D.minimum F.minimum
--           D.shape.sigma F.shape.sigma D.shape.rho F.shape.rho
--           (weylGradientEnergy Z) (weylGradientEnergy V) p q
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Angular.Gradient`, `OAI.PositiveEinsteinFour.Angular.Mat3`, `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.TraceHessian.Mat`, `OAI.PositiveEinsteinFour.TraceHessian.symmetric` and `OAI.PositiveEinsteinFour.TraceHessian.traceFree` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Energy.scalarWeight` (definitions bundle `OAIQ091C001` of this split); `OAI.PositiveEinsteinFour.Bianchi.Shape.rho` and `OAI.PositiveEinsteinFour.Bianchi.Shape.sigma` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.Geometry.gradientDivergence` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.reducedIntegrand` (definitions bundle `OAIQ091C012` of this split); `OAI.PositiveEinsteinFour.Geometry.weylGradientEnergy` (definitions bundle `OAIQ091C015` of this split); `OAI.PositiveEinsteinFour.QuaternionFrame.PointwiseSpectrum` and `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand` (definitions bundle `OAIQ091C018` of this split); `OAI.PositiveEinsteinFour.Geometry.normalizedBlockNorm` (definitions bundle `OAIQ091C036` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean (declaration OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C018

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential Boundary

noncomputable section

theorem arrayCoupledIntegrand_le_reduced
    (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
    (hZb : ∀ r i, gradientDivergence Z r i = 0)
    (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
    (hVb : ∀ r i, gradientDivergence V r i = 0)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hzerob : normalizedBlockNorm U = 0 → V = 0)
    (D : PointwiseSpectrum A U Z p) (F : PointwiseSpectrum U A V q)
    (hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
      ‖p - q‖ ^ 2)
    (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
      ‖p - q‖ ^ 2) :
    arrayCoupledIntegrand A U Z V a ab p q ≤
      reducedIntegrand (normalizedBlockNorm A) (normalizedBlockNorm U) D.minimum F.minimum
        D.shape.sigma F.shape.sigma D.shape.rho F.shape.rho
        (weylGradientEnergy Z) (weylGradientEnergy V) p q := by
  sorry

end
end PositiveEinsteinFour.QuaternionFrame
end

end OAI
end
