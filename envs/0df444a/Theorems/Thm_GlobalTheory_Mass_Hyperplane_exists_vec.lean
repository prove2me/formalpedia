-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_exists_vec
-- name    : GlobalTheory.Mass.Hyperplane.exists_vec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:10.392843+00:00
-- url     : https://prove2.me/theorems/c7322f17-c812-4475-bc3f-6c4a7af8279a
-- title:
--   Hyperplane: exists vec
-- statement:
--   The Hyperplane construction uses the exists vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L287-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L287-L316

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [NumberField K]

theorem GlobalTheory.Mass.Hyperplane.exists_vec [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (h x y) = h y x)
    (hn : h.Nondegenerate) {M L : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hU : IsUnimodularAt h P M) (hL : L ≤ M)
    (φ : (↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) :
    ∃ u ∈ loc (K := K) P M, (∃ w ∈ loc (K := K) P M, h u w ∉ locId P) ∧
      ∀ x, x ∈ loc (K := K) P L ↔ x ∈ loc (K := K) P M ∧ h u x ∈ locId P := by sorry
