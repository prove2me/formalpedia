-- Prove2me | Theorems.Thm_GlobalTheory_Mass_finrank_le_trace_of_integral
-- name    : GlobalTheory.Mass.finrank_le_trace_of_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:55.438699+00:00
-- url     : https://prove2.me/theorems/58ea6854-d009-44e3-83fc-c251982bb34f
-- title:
--   Mass: finrank le trace of integral
-- statement:
--   The Mass construction uses the finrank le trace of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardShortVectorsLe.lean#L27-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardShortVectorsLe.lean#L27-L49

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

theorem GlobalTheory.Mass.finrank_le_trace_of_integral {K : Type} [Field K] [NumberField K] (z : 𝓞 K)
    (hre : ∀ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).im = 0) (hpos : ∀ τ : K →ₐ[ℚ] ℂ, 0 < (τ (z : K)).re) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by sorry
