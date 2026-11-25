-- Prove2me | Theorems.Thm_GlobalTheory_T_few_orbits_subspaces_hermitian_lattice_discriminant
-- name    : GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:03.593916+00:00
-- url     : https://prove2.me/theorems/7ede78fb-e099-40aa-9918-bc85c588b5a4
-- title:
--   T: few orbits subspaces hermitian lattice discriminant
-- statement:
--   The T construction uses the few orbits subspaces hermitian lattice discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FewOrbitsSubspacesHermitianLatticeDiscriminantStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FewOrbitsSubspacesHermitianLatticeDiscriminantStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FewOrbitsSubspacesHermitianLatticeDiscriminant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FewOrbitsSubspacesHermitianLatticeDiscriminantStatement
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

theorem GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j n : ℕ), 1 ≤ n → ∃ s : Finset (Submodule K V), (s.card : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (Module.finrank ℚ K)) ∧ (∀ U ∈ s, Module.finrank K U = j) ∧ ∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) n).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U := by sorry
