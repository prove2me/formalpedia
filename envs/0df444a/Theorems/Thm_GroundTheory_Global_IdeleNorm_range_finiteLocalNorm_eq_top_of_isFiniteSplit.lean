-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_range_finiteLocalNorm_eq_top_of_isFiniteSplit
-- name    : GroundTheory.Global.IdeleNorm.range_finiteLocalNorm_eq_top_of_isFiniteSplit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:48.306085+00:00
-- url     : https://prove2.me/theorems/e123c224-d248-5855-86b1-0041186b13c8
-- title:
--   Idele Norm: range finite Local Norm eq top of is Finite Split
-- statement:
--   The Idele Norm construction uses the range finite Local Norm eq top of is Finite Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L113-L120

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
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
open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.IdeleNorm.range_finiteLocalNorm_eq_top_of_isFiniteSplit (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)) :
    (finiteLocalNorm L v).range = ⊤ := by sorry
