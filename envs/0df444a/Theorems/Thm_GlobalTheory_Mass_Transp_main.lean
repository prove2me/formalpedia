-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Transp_main
-- name    : GlobalTheory.Mass.Transp.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:43.617665+00:00
-- url     : https://prove2.me/theorems/f2d1e080-2f09-4259-b77a-3f196f4e604b
-- title:
--   Transp: main
-- statement:
--   The Transp construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatsDiscStable.lean#L286-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatsDiscStable.lean#L286-L296

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
import Theorems.Thm_GlobalTheory_Mass_OrbTransport_main

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Transp

theorem GlobalTheory.Mass.Transp.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ e : V ≃ₗ[K] V', (∀ x y, h' (e x) (e y) = h x y) → (∀ n : ℕ, orbMass (isom h) (latsDisc (R := 𝓞 K) h n) = orbMass (isom h') (latsDisc (R := 𝓞 K) h' n)) ∧ ∀ L : Submodule (𝓞 K) V, orbMass (isom h) (genus h L) = orbMass (isom h') (genus h' (L.map (e.toLinearMap.restrictScalars (𝓞 K)))) ∧ discN h' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = discN h L ∧ (IsIntLat h' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) ↔ IsIntLat h L) := by sorry
