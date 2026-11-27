-- Prove2me | Theorems.Thm_GroundTheory_Global_absNorm_relDiscr_rat
-- name    : GroundTheory.Global.absNorm_relDiscr_rat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:55.998628+00:00
-- url     : https://prove2.me/theorems/35785fe9-1031-505e-b11b-70e15dbfa823
-- title:
--   Global: abs Norm rel Discr rat
-- statement:
--   The Global construction uses the abs Norm rel Discr rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L146-L148

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable (M : Type*) [Field M] [NumberField M]

theorem GroundTheory.Global.absNorm_relDiscr_rat : Ideal.absNorm (relDiscr ℚ M) = (discr M).natAbs := by sorry
