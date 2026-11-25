-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_infiniteLocalNorm
-- name    : GroundTheory.Global.IdeleNorm.coe_infiniteLocalNorm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:14.000725+00:00
-- url     : https://prove2.me/theorems/65405344-a7ed-412d-9071-6b40fca72945
-- title:
--   Idele Norm: coe infinite Local Norm
-- statement:
--   The Idele Norm construction uses the coe infinite Local Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L60-L64

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
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
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
omit [NumberField K]
open scoped Classical
variable {L}

theorem GroundTheory.Global.IdeleNorm.coe_infiniteLocalNorm (v : InfinitePlace K)
    (y : (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    ((infiniteLocalNorm L v y : (v.Completion)ˣ) : v.Completion) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y w : (w : InfinitePlace L).Completion) := by sorry
