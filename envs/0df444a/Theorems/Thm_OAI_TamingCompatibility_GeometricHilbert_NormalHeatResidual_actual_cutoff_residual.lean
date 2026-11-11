-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_actual_cutoff_residual
-- name    : OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:19:08.899696+00:00
-- url     : https://prove2.me/theorems/b0293e40-7635-4ea9-a10f-ddd92f8f36a6
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCutoffBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCutoffBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual`, with `open OperatorCalculus FlatHeat`, `open scoped ContDiff`):
--
--   ```lean
--   lemma actual_cutoff_residual (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
--       (ρ : V → ℝ) (g : Fin 4 → Fin 4 → V → ℝ) (U : V → W →L[ℝ] W)
--       (hU : ContDiff ℝ ∞ U) (horth : ∀ z, (U z).adjoint ∘L U z = ContinuousLinearMap.id ℝ W)
--       (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
--       {z : V} (ha : ∀ i, DifferentiableAt ℝ (a i) z) (hb : DifferentiableAt ℝ b z)
--       (hρ : DifferentiableAt ℝ ρ z) (hρz : ρ z ≠ 0)
--       (hp : ∀ i j, (a i z).adjoint ∘L a j z + (a j z).adjoint ∘L a i z =
--         (2*g i j z) • ContinuousLinearMap.id ℝ W) {t : ℝ} (ht : 0 < t) (u : W) :
--       (U z).adjoint (deriv (fun s => U z (χ z • modelSection s u z)) t +
--         weightedAdjoint (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ
--           (differential (EuclideanSpace.basisFun (Fin 4) ℝ) a b
--             (fun y => U y (χ y • modelSection t u y))) z) =
--         deriv (fun s => χ z • modelSection s u z) t +
--           secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) g
--             (gaugeFirst (EuclideanSpace.basisFun (Fin 4) ℝ) g
--               (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
--             (gaugeZero (EuclideanSpace.basisFun (Fin 4) ℝ) g
--               (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ)
--               (zeroMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
--             (fun y => χ y • modelSection t u y) z
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.firstMatrix`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.gaugeFirst`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.gaugeZero` and `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.zeroMatrix` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.differential`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.secondOrder` and `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.weightedAdjoint` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.modelSection` (definitions bundle `OAIQ239Tc008` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCutoffBounds.lean (declaration OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual)

import Mathlib
import Definitions.Def_OAIQ239Tc008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat
open scoped ContDiff
variable {W Q : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma actual_cutoff_residual (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (g : Fin 4 → Fin 4 → V → ℝ) (U : V → W →L[ℝ] W)
    (hU : ContDiff ℝ ∞ U) (horth : ∀ z, (U z).adjoint ∘L U z = ContinuousLinearMap.id ℝ W)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {z : V} (ha : ∀ i, DifferentiableAt ℝ (a i) z) (hb : DifferentiableAt ℝ b z)
    (hρ : DifferentiableAt ℝ ρ z) (hρz : ρ z ≠ 0)
    (hp : ∀ i j, (a i z).adjoint ∘L a j z + (a j z).adjoint ∘L a i z =
      (2*g i j z) • ContinuousLinearMap.id ℝ W) {t : ℝ} (ht : 0 < t) (u : W) :
    (U z).adjoint (deriv (fun s => U z (χ z • modelSection s u z)) t +
      weightedAdjoint (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ
        (differential (EuclideanSpace.basisFun (Fin 4) ℝ) a b
          (fun y => U y (χ y • modelSection t u y))) z) =
      deriv (fun s => χ z • modelSection s u z) t +
        secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) g
          (gaugeFirst (EuclideanSpace.basisFun (Fin 4) ℝ) g
            (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
          (gaugeZero (EuclideanSpace.basisFun (Fin 4) ℝ) g
            (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ)
            (zeroMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
          (fun y => χ y • modelSection t u y) z := by
  sorry

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end
