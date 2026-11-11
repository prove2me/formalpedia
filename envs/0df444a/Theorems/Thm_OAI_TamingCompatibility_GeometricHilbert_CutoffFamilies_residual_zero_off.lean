-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_CutoffFamilies_residual_zero_off
-- name    : OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:11.547527+00:00
-- url     : https://prove2.me/theorems/268041db-1428-4525-be03-83724b965861
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off` of [lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeCutoffResidual.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeCutoffResidual.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies`, with `open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma residual_zero_off (a : Fin 4 → Fin 4 → P × V → ℝ)
--       (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
--       (χ : V → ℝ) (q : P) (t : ℝ) {z : V} (hz : z ∉ tsupport χ) :
--       residual (fun y => principal a χ (q,y)) (fun y => first a b χ (q,y))
--         (fun y => zero a b c χ (q,y)) t z = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.first`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.principal`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.zero`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.End` and `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.residual` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFiberForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_domain` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeCutoffResidual.lean (declaration OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma residual_zero_off (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) (q : P) (t : ℝ) {z : V} (hz : z ∉ tsupport χ) :
    residual (fun y => principal a χ (q,y)) (fun y => first a b χ (q,y))
      (fun y => zero a b c χ (q,y)) t z = 0 := by
  sorry

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
end
