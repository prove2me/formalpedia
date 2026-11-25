-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_exists_norm_eq_of_ramificationIdx_eq_one
-- name    : GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:13.532116+00:00
-- url     : https://prove2.me/theorems/6fe6e903-fc37-53aa-98dd-c4a0c74d12bf
-- title:
--   Idele Norm: exists norm eq of ramification Idx eq one
-- statement:
--   The Idele Norm construction uses the exists norm eq of ramification Idx eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L122-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L122-L141

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

theorem GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ∃ y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units,
      Algebra.norm (v.adicCompletion K) (y : w.adicCompletion L) = u := by sorry
