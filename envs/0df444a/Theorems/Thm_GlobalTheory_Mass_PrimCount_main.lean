-- Prove2me | Theorems.Thm_GlobalTheory_Mass_PrimCount_main
-- name    : GlobalTheory.Mass.PrimCount.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:04.724967+00:00
-- url     : https://prove2.me/theorems/4470e504-cda4-5fea-ba72-001e89bb0aca
-- title:
--   Prim Count: main
-- statement:
--   The Prim Count construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatInIsLattice.lean#L70-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatInIsLattice.lean#L70-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatInIsLattice
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_ShortVector_main

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimCount

theorem GlobalTheory.Mass.PrimCount.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ n : ℕ, 1 ≤ n → (((primSp h L 1 n).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((9 * (2 * vInv K)) ^ (Module.finrank K V * fDeg K) * (n : ℝ) ^ ((Module.finrank K V : ℝ) / 2)) ∧ (primSp h L 0 n).encard ≤ 1 := by sorry
