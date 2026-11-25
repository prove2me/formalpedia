-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_piPlacesOverBasis_repr
-- name    : GroundTheory.Global.AdeleBaseChange.piPlacesOverBasis_repr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:37.196149+00:00
-- url     : https://prove2.me/theorems/9436eba9-c7cc-54ca-becf-97788b2904e5
-- title:
--   Adele Base Change: pi Places Over Basis repr
-- statement:
--   The Adele Base Change construction uses the pi Places Over Basis repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean#L85-L88

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
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
open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

theorem GroundTheory.Global.AdeleBaseChange.piPlacesOverBasis_repr (v : InfinitePlace K)
    (z : GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) (i : ι) :
    (piPlacesOverBasis b v).repr z i = GroundTheory.Global.InfinitePlace.piPlacesOverCoord b v i z := by sorry
