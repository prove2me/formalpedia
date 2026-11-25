-- Prove2me | Theorems.Thm_GlobalTheory_T_maximalHermitianLattice_badPrimes_iff_gramDet
-- name    : GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:17:00.439714+00:00
-- url     : https://prove2.me/theorems/d72ee584-44b0-54c5-913a-ea6d8e5609a1
-- title:
--   T: maximal Hermitian Lattice bad Primes iff gram Det
-- statement:
--   The T construction uses the maximal Hermitian Lattice bad Primes iff gram Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDetStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDetStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
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

theorem GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ (j : ℕ) (b : Module.Basis (Fin j) K V) (P : Ideal (𝓞 K)), P.IsMaximal → (P ∈ badP h M ↔ conjIdeal (K := K) P = P ∧ ¬ ∃ c : K, c ≠ 0 ∧ star c * c * (Matrix.of fun i l => h (b i) (b l)).det ∈ locR (K := K) P ∧ (star c * c * (Matrix.of fun i l => h (b i) (b l)).det)⁻¹ ∈ locR (K := K) P) := by sorry
