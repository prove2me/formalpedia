-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_short_vector_integralHermitianLattice_rank_one
-- name    : GlobalTheory.T.exists_short_vector_integralHermitianLattice_rank_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:46:12.115605+00:00
-- url     : https://prove2.me/theorems/3b7ce57a-9a12-42b1-b2f3-c14534408040
-- title:
--   T: exists short vector integral Hermitian Lattice rank one
-- statement:
--   The T construction uses the exists short vector integral Hermitian Lattice rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOneStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOneStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOneStatement
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

theorem GlobalTheory.T.exists_short_vector_integralHermitianLattice_rank_one : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ x ∈ M, x ≠ 0 ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ (2 * vInv K) * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) := by sorry
