-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_map_integerUnitsOver_le
-- name    : GroundTheory.Global.IdeleNorm.map_integerUnitsOver_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:13.249821+00:00
-- url     : https://prove2.me/theorems/3f255ec1-0111-545b-8cc6-a7e048ee0043
-- title:
--   Idele Norm: map integer Units Over le
-- statement:
--   The Idele Norm construction uses the map integer Units Over le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L95-L101

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

theorem GroundTheory.Global.IdeleNorm.map_integerUnitsOver_le (v : HeightOneSpectrum (𝓞 K)) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) ≤
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by sorry
