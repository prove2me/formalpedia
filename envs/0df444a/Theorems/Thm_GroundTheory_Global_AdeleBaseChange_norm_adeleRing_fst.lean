-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_fst
-- name    : GroundTheory.Global.AdeleBaseChange.norm_adeleRing_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:37.913302+00:00
-- url     : https://prove2.me/theorems/3f027de9-5792-5c2a-88d3-aa3579163493
-- title:
--   Adele Base Change: norm adele Ring fst
-- statement:
--   The Adele Base Change construction uses the norm adele Ring fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean#L102-L105

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
open scoped Classical

theorem GroundTheory.Global.AdeleBaseChange.norm_adeleRing_fst (v : InfinitePlace K) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y.1 w) := by sorry
