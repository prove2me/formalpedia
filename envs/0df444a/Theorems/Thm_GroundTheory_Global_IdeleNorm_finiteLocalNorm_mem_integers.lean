-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mem_integers
-- name    : GroundTheory.Global.IdeleNorm.finiteLocalNorm_mem_integers
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:25.317718+00:00
-- url     : https://prove2.me/theorems/d3537995-dd7b-5ea4-af88-ef04ce17f365
-- title:
--   Idele Norm: finite Local Norm mem integers
-- statement:
--   The Idele Norm construction uses the finite Local Norm mem integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L86-L93

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

theorem GroundTheory.Global.IdeleNorm.finiteLocalNorm_mem_integers {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} (hy : y ∈ integerUnitsOver L v) :
    (finiteLocalNorm L v y : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by sorry
