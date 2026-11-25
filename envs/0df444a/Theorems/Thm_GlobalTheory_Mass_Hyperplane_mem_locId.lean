-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_mem_locId
-- name    : GlobalTheory.Mass.Hyperplane.mem_locId
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:49.762031+00:00
-- url     : https://prove2.me/theorems/2994dd99-0177-5b50-bec5-2b49af02cc57
-- title:
--   Hyperplane: mem loc Id
-- statement:
--   The Hyperplane construction uses the mem loc Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L187-L190

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

theorem GlobalTheory.Mass.Hyperplane.mem_locId {P : Ideal (𝓞 K)} {x : K} :
    x ∈ locId P ↔ ∃ s ∈ hcompl (K := K) P, ∃ r ∈ P, algebraMap _ K r = algebraMap _ K s * x := by sorry
