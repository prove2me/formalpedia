-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_main
-- name    : GlobalTheory.Mass.Hyperplane.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:50.457207+00:00
-- url     : https://prove2.me/theorems/b57cf5e6-29fe-45d7-84ea-71fea8b60917
-- title:
--   Hyperplane: main
-- statement:
--   The Hyperplane construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L320-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L320-L363

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

theorem GlobalTheory.Mass.Hyperplane.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P ≠ P → IsUnimodularAt h P M → ∀ L L' : Submodule (𝓞 K) V, L ≤ M → L' ≤ M → Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) → Nonempty ((↥M ⧸ L'.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) → ∃ g ∈ isom h, gmap g (loc (K := K) P M) = loc (K := K) P M ∧ gmap g (loc (K := K) P L) = loc (K := K) P L' := by sorry
