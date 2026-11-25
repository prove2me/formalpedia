-- Prove2me | Theorems.Thm_GlobalTheory_T_maximalLatticeLocalFactorProduct_pos_and_le
-- name    : GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:49.016285+00:00
-- url     : https://prove2.me/theorems/e7a871fb-6b34-4b4d-be7c-ee3792a141f9
-- title:
--   T: maximal Lattice Local Factor Product pos and le
-- statement:
--   The T construction uses the maximal Lattice Local Factor Product pos and le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalLatticeLocalFactorProductPosAndLeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalLatticeLocalFactorProductPosAndLeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalLatticeLocalFactorProductPosAndLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalLatticeLocalFactorProductPosAndLeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → 1 ≤ Module.finrank K V → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → 0 < lamMax h M ∧ lamMax h M ≤ (discN h M : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by sorry
