-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Gal_localEuler_places
-- name    : GlobalTheory.CompanionTheory.Gal.localEuler_places
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:34.666438+00:00
-- url     : https://prove2.me/theorems/417365cd-4c1a-4a74-8f34-392c0d3752fd
-- title:
--   Gal: local Euler places
-- statement:
--   The Gal construction uses the local Euler places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalEulerPlaces.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalEulerPlaces.lean#L8-L10

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalEulerPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Gal

theorem GlobalTheory.CompanionTheory.Gal.localEuler_places : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalEulerChar → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, (((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal → Nat.card (H1 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v))) * Nat.card M ^ locDeg v.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.1.asIdeal → Nat.card (H1 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v)))) := by sorry
