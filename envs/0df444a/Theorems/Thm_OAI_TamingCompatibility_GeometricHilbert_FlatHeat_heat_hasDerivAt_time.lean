-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_hasDerivAt_time
-- name    : OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:08.589829+00:00
-- url     : https://prove2.me/theorems/ac7f9086-2312-492b-92b0-e36e7f9e3fad
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time` of [lean/OAI/Geometry/TamingCompatibility/HeatFlow/FlatHeat.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/FlatHeat.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.FlatHeat`, with `open _root_.MeasureTheory Set`, `open scoped RealInnerProductSpace ContDiff`):
--
--   ```lean
--   lemma heat_hasDerivAt_time {t : ℝ} (ht : 0 < t) (z : V) :
--       HasDerivAt (fun s => heat s z) ((-2/t+‖z‖^2/(4*t^2))*heat t z) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V` and `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/FlatHeat.lean (declaration OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

lemma heat_hasDerivAt_time {t : ℝ} (ht : 0 < t) (z : V) :
    HasDerivAt (fun s => heat s z) ((-2/t+‖z‖^2/(4*t^2))*heat t z) t := by
  sorry

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end
