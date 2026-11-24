-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PoitouTateCount_card_sha2_mul_card_local_h2
-- name    : GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:05.073958+00:00
-- url     : https://prove2.me/theorems/647ce355-2c05-48c3-ba0c-d97823c3dfa5
-- title:
--   Poitou Tate Count: card sha2 mul card local h2
-- statement:
--   The Poitou Tate Count construction uses the card sha2 mul card local h2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateNineTermExact.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateNineTermExact.lean#L12-L29

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NatCardDualEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardEqCardKerMulCardRange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDualStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristicStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateNineTermExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PoitouTateCount

theorem GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2 : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → Finite (H2 ρ) → Finite (H0 (twDual μ ρ)) → Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) * Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) = Nat.card (H2 ρ) * Nat.card (H0 (twDual μ ρ)) := by sorry
