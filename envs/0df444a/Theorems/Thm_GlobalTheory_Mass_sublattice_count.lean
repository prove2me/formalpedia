-- Prove2me | Theorems.Thm_GlobalTheory_Mass_sublattice_count
-- name    : GlobalTheory.Mass.sublattice_count
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:18.272511+00:00
-- url     : https://prove2.me/theorems/0898a0f6-d93f-42a2-93b5-e9222d86033f
-- title:
--   Mass: sublattice count
-- statement:
--   The Mass construction uses the sublattice count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardSublatticesOfIndexLe.lean#L10-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardSublatticesOfIndexLe.lean#L10-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesOfIndexLe
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

theorem GlobalTheory.Mass.sublattice_count : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by sorry
