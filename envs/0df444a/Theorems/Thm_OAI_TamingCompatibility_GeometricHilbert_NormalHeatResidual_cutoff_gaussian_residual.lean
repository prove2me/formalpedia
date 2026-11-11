-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_cutoff_gaussian_residual
-- name    : OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:18:43.5689+00:00
-- url     : https://prove2.me/theorems/3d964bd9-3dd6-4b24-badc-9fe227968d68
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCutoffSquare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCutoffSquare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual`, with `open OperatorCalculus FlatHeat Filter Set`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma cutoff_gaussian_residual (a : Fin 4 → Fin 4 → V → ℝ)
--       (b : Fin 4 → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
--       (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (ht : 0 < t) (z : V) (u : W) :
--       deriv (fun s => χ z • modelSection s u z) t +
--         secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) a b c
--           (fun y => χ y • modelSection t u y) z =
--         residual (fun y i j => cutoffPrincipal a χ i j y)
--           (fun y j => cutoffFirst (EuclideanSpace.basisFun (Fin 4) ℝ) a b χ j y)
--           (cutoffZero (EuclideanSpace.basisFun (Fin 4) ℝ) a b c χ) t z u
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.End`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoffPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.residual`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.cutoffFirst` and `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.cutoffZero` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.secondOrder` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.modelSection` (definitions bundle `OAIQ239Tc008` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq` and `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCutoffSquare.lean (declaration OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual)

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
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma cutoff_gaussian_residual (a : Fin 4 → Fin 4 → V → ℝ)
    (b : Fin 4 → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (ht : 0 < t) (z : V) (u : W) :
    deriv (fun s => χ z • modelSection s u z) t +
      secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) a b c
        (fun y => χ y • modelSection t u y) z =
      residual (fun y i j => cutoffPrincipal a χ i j y)
        (fun y j => cutoffFirst (EuclideanSpace.basisFun (Fin 4) ℝ) a b χ j y)
        (cutoffZero (EuclideanSpace.basisFun (Fin 4) ℝ) a b c χ) t z u := by
  sorry

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end
