-- Prove2me | Theorems.Thm_GlobalTheory_cechOpen_pair
-- name    : GlobalTheory.cechOpen_pair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:34.402716+00:00
-- url     : https://prove2.me/theorems/11bf137d-de4d-4c87-b50d-68b37e94d33e
-- title:
--   Global Theory: cech Open pair
-- statement:
--   The Global Theory construction uses the cech Open pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L60-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : Type w} [TopologicalSpace T] {ι κ : Type}
variable (V : Opens T) (U : ι → Opens T)

theorem GlobalTheory.cechOpen_pair [DecidableEq ι] (i j : ι) : cechOpen V U {i, j} = V ⊓ (U i ⊓ U j) := by sorry
