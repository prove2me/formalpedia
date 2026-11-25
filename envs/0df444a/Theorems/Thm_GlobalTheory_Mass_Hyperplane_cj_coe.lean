-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_cj_coe
-- name    : GlobalTheory.Mass.Hyperplane.cj_coe
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:04:07.327817+00:00
-- url     : https://prove2.me/theorems/a2318bfb-511d-53c5-b403-0a9f1b28f191
-- title:
--   Hyperplane: cj coe
-- statement:
--   The Hyperplane construction uses the cj coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L120-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L120-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K : Type} [Field K] [StarRing K]

theorem GlobalTheory.Mass.Hyperplane.cj_coe (s : 𝓞 K) : algebraMap (𝓞 K) K (cj K s) = star (algebraMap (𝓞 K) K s) := by sorry
