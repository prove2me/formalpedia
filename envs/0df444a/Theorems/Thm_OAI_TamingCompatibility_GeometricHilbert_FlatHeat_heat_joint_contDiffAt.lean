-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_joint_contDiffAt
-- name    : OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_joint_contDiffAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:09.088043+00:00
-- url     : https://prove2.me/theorems/0cc63ef7-af20-4e6e-a609-86a9063fa524
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_joint_contDiffAt: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_joint_contDiffAt` of [lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeHeatJointSmooth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeHeatJointSmooth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.FlatHeat`, with `open scoped ContDiff`):
--
--   ```lean
--   lemma heat_joint_contDiffAt {x : ℝ × V} (hx : x.1 ≠ 0) :
--       ContDiffAt ℝ ∞ (fun v : ℝ × V => heat v.1 v.2) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V` and `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_continuousAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_smooth` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeHeatJointSmooth.lean (declaration OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_joint_contDiffAt)

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
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open scoped ContDiff

lemma heat_joint_contDiffAt {x : ℝ × V} (hx : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : ℝ × V => heat v.1 v.2) x := by
  sorry

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

end

end OAI
end
