-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_exists_form
-- name    : GlobalTheory.Mass.Hyperplane.exists_form
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:58.700005+00:00
-- url     : https://prove2.me/theorems/c73de51e-c2f7-53f5-bd26-86769812161f
-- title:
--   Hyperplane: exists form
-- statement:
--   The Hyperplane construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L261-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L261-L285

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
omit [StarRing K]

theorem GlobalTheory.Mass.Hyperplane.exists_form {M L : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) {P : Ideal (𝓞 K)}
    (φ : (↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) :
    ∃ (f : V →ₗ[K] K) (ψ : M →ₗ[𝓞 K] 𝓞 K), (∀ y : M, f y = algebraMap (𝓞 K) K (ψ y)) ∧
      ∀ y : M, ψ y ∈ P ↔ (y : V) ∈ L := by sorry
