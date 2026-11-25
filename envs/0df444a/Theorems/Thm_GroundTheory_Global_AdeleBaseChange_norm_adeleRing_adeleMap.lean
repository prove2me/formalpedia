-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_adeleMap
-- name    : GroundTheory.Global.AdeleBaseChange.norm_adeleRing_adeleMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:21:54.566658+00:00
-- url     : https://prove2.me/theorems/4d239bd2-955a-5e08-9660-2fce7c031564
-- title:
--   Adele Base Change: norm adele Ring adele Map
-- statement:
--   The Adele Base Change construction uses the norm adele Ring adele Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L115-L118

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
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

theorem GroundTheory.Global.AdeleBaseChange.norm_adeleRing_adeleMap (x : 𝔸[K]) :
    Algebra.norm 𝔸[K] (adeleMap K L x) = x ^ Module.finrank K L := by sorry
