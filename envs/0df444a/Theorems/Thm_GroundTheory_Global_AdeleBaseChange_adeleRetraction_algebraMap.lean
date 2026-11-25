-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleRetraction_algebraMap
-- name    : GroundTheory.Global.AdeleBaseChange.adeleRetraction_algebraMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:47.308096+00:00
-- url     : https://prove2.me/theorems/fad31b92-c905-4290-a195-3898c2f990aa
-- title:
--   Adele Base Change: adele Retraction algebra Map
-- statement:
--   The Adele Base Change construction uses the adele Retraction algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L120-L126

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

theorem GroundTheory.Global.AdeleBaseChange.adeleRetraction_algebraMap (l : L) :
    adeleRetraction K L (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (normalizedTrace K L l) := by sorry
