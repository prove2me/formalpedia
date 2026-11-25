-- Prove2me | Theorems.Thm_GlobalTheory_Mass_LocWitt_main
-- name    : GlobalTheory.Mass.LocWitt.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:42.162369+00:00
-- url     : https://prove2.me/theorems/82f11b3c-9f6d-5f2b-b45d-6bbedbd0e719
-- title:
--   Loc Witt: main
-- statement:
--   The Loc Witt construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L182-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L182-L262

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt

theorem GlobalTheory.Mass.LocWitt.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L : Submodule (𝓞 K) V), Submodule.IsLattice K L → ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P = P → IsUnimodularAt h P L → ∀ x ∈ loc (K := K) P L, ∀ y ∈ loc (K := K) P L, h x x = h y y → (∃ w ∈ loc (K := K) P L, h w x = 1) → (∃ w ∈ loc (K := K) P L, h w y = 1) → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L ∧ g x = y := by sorry
