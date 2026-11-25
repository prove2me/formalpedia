-- Prove2me | Theorems.Thm_GlobalTheory_DI_phi_mem_forms
-- name    : GlobalTheory.DI.phi_mem_forms
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:28.526234+00:00
-- url     : https://prove2.me/theorems/d012303e-982f-4c1a-a67b-8b0628e2049d
-- title:
--   DI: phi mem forms
-- statement:
--   The DI construction uses the phi mem forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/SplittingIntegralFormsBound.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/SplittingIntegralFormsBound.lean#L21-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductIntegral
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_SplittingIntegralFormsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI

theorem GlobalTheory.DI.phi_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by sorry
