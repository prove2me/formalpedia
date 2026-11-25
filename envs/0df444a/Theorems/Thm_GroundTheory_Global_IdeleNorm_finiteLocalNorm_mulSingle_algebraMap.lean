-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mulSingle_algebraMap
-- name    : GroundTheory.Global.IdeleNorm.finiteLocalNorm_mulSingle_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:36.998909+00:00
-- url     : https://prove2.me/theorems/6a33f16c-6681-51f9-916e-3e71e0bae714
-- title:
--   Idele Norm: finite Local Norm mul Single algebra Map
-- statement:
--   The Idele Norm construction uses the finite Local Norm mul Single algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormGroups.lean#L103-L111

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

theorem GroundTheory.Global.IdeleNorm.finiteLocalNorm_mulSingle_algebraMap (v : HeightOneSpectrum (𝓞 K))
    [DecidableEq (PlacesOver L v)] (w : PlacesOver L v) (a : (v.adicCompletion K)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w (Units.map (algebraMap (v.adicCompletion K)
      (w.1.adicCompletion L) : v.adicCompletion K →* w.1.adicCompletion L) a)) =
        a ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by sorry
