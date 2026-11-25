-- Prove2me | Theorems.Thm_GlobalTheory_Mass_finrank_le_of_span_range
-- name    : GlobalTheory.Mass.finrank_le_of_span_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:39:14.620813+00:00
-- url     : https://prove2.me/theorems/91ded532-d1dd-4aff-8ab5-74c4e691fbee
-- title:
--   Mass: finrank le of span range
-- statement:
--   The Mass construction uses the finrank le of span range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardShortVectorsLe.lean#L51-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardShortVectorsLe.lean#L51-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLe
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
open GlobalTheory GlobalTheory.Mass

theorem GlobalTheory.Mass.finrank_le_of_span_range {K V E : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module ℝ E] (ι : V →+ E)
    (hs : Submodule.span ℝ (Set.range ι) = ⊤) :
    Module.finrank ℝ E ≤ Module.finrank ℚ K * Module.finrank K V := by sorry
