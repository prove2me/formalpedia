-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleClassNorm_mk
-- name    : GroundTheory.Global.ideleClassNorm_mk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:21:17.963814+00:00
-- url     : https://prove2.me/theorems/35845a75-ea11-5ce5-8e74-a7459d1d9acf
-- title:
--   Global: idele Class Norm mk
-- statement:
--   The Global construction uses the idele Class Norm mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L216-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L216-L218

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

theorem GroundTheory.Global.ideleClassNorm_mk (x : IdeleGroup L) :
    ideleClassNorm K L (IdeleClassGroup.mk L x) = IdeleClassGroup.mk K (ideleNorm K L x) := by sorry

attribute [defeq] GroundTheory.Global.ideleClassNorm_mk
