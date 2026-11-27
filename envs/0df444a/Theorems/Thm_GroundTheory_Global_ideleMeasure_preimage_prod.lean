-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleMeasure_preimage_prod
-- name    : GroundTheory.Global.ideleMeasure_preimage_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:52.107454+00:00
-- url     : https://prove2.me/theorems/5f252a07-8e9d-588c-9ff3-367dc46a89f7
-- title:
--   Global: idele Measure preimage prod
-- statement:
--   The Global construction uses the idele Measure preimage prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L471-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L471-L476

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.ideleMeasure_preimage_prod {A : Set (InfiniteAdeleRing K)ˣ}
    {B : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ideleMeasure K (IdeleGroup.prodEquiv K ⁻¹' (A ×ˢ B)) =
      infiniteIdeleMeasure K A * finiteIdeleMeasure K B := by sorry
