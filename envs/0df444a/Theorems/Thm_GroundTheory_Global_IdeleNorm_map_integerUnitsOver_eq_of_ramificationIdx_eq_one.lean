-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_map_integerUnitsOver_eq_of_ramificationIdx_eq_one
-- name    : GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:58.851861+00:00
-- url     : https://prove2.me/theorems/4ad0adab-9d82-47fb-b11c-dbf2e80948a8
-- title:
--   Idele Norm: map integer Units Over eq of ramification Idx eq one
-- statement:
--   The Idele Norm construction uses the map integer Units Over eq of ramification Idx eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L28-L43

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormsEverywhere
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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : PlacesOver L v) (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) =
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by sorry
