-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Galois_PlacesOfS_localFinite_at_places
-- name    : GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:43.290702+00:00
-- url     : https://prove2.me/theorems/223f9e61-a3a5-4e73-a2da-cad9c4e36daf
-- title:
--   Places Of S: local Finite at places
-- statement:
--   The Places Of S construction uses the local Finite at places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaloisCohomologyLocalGlobalDual.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaloisCohomologyLocalGlobalDual.lean#L11-L15

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Galois GlobalTheory.CompanionTheory.Galois.PlacesOfS

theorem GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Finite (H0 (ρ.comp (locFam S Av v))) ∧ Finite (H1 (ρ.comp (locFam S Av v))) ∧ Finite (H2 (ρ.comp (locFam S Av v))) := by sorry
