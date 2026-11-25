-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_main
-- name    : GlobalTheory.MaxLatStruct.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:09.025104+00:00
-- url     : https://prove2.me/theorems/a4db82e5-16f3-4a2a-b57b-7a461f7c7f6b
-- title:
--   Max Lat Struct: main
-- statement:
--   The Max Lat Struct construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L511-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L511-L550

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
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
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct

theorem GlobalTheory.MaxLatStruct.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → (badP h M).Finite ∧ discN h M = ∏ᶠ P ∈ badP h M, Ideal.absNorm P ∧ Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ᶠ P ∈ badP h M, P)) ∧ ∀ P ∈ badP h M, conjIdeal (K := K) P = P ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 ∧ ∃ x ∈ M, (∃ a : 𝓞 K, (a : K) = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧ ∀ y ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, y - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by sorry
