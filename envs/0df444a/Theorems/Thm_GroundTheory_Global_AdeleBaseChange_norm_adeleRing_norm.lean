-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_norm
-- name    : GroundTheory.Global.AdeleBaseChange.norm_adeleRing_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:03:11.096347+00:00
-- url     : https://prove2.me/theorems/839d6374-871f-5109-8657-e105943f357c
-- title:
--   Adele Base Change: norm adele Ring norm
-- statement:
--   The Adele Base Change construction uses the norm adele Ring norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L98-L100

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap
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
open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem GroundTheory.Global.AdeleBaseChange.norm_adeleRing_norm (y : 𝔸[M]) :
    Algebra.norm 𝔸[K] (Algebra.norm 𝔸[L] y) = Algebra.norm 𝔸[K] y := by sorry
