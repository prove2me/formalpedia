-- Prove2me | Theorems.Thm_GroundTheory_Global_continuous_ideleClassNorm
-- name    : GroundTheory.Global.continuous_ideleClassNorm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:14.511852+00:00
-- url     : https://prove2.me/theorems/c095f24f-c255-5f9a-85e4-07e5af41ecf9
-- title:
--   Global: continuous idele Class Norm
-- statement:
--   The Global construction uses the continuous idele Class Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L224-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L224-L226

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}

theorem GroundTheory.Global.continuous_ideleClassNorm : Continuous (ideleClassNorm K L) := by sorry
