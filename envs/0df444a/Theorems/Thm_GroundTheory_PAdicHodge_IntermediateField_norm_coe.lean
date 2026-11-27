-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IntermediateField_norm_coe
-- name    : GroundTheory.PAdicHodge.IntermediateField.norm_coe
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:13:23.265724+00:00
-- url     : https://prove2.me/theorems/5280ae98-829e-43d6-833a-7f7a40ea03bd
-- title:
--   Intermediate Field: norm coe
-- statement:
--   The Intermediate Field construction uses the norm coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L150-L151

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]

theorem GroundTheory.PAdicHodge.IntermediateField.norm_coe (F : IntermediateField K C) (x : F) : ‖(x : C)‖ = ‖x‖ := by sorry
