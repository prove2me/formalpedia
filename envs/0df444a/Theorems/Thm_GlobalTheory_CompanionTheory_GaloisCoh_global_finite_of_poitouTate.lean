-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaloisCoh_global_finite_of_poitouTate
-- name    : GlobalTheory.CompanionTheory.GaloisCoh.global_finite_of_poitouTate
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:23.186156+00:00
-- url     : https://prove2.me/theorems/41b1cac0-2be0-4893-bc4a-50594a9d0196
-- title:
--   Galois Coh: global finite of poitou Tate
-- statement:
--   The Galois Coh construction uses the global finite of poitou Tate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesFormula.lean#L30-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesFormula.lean#L30-L59

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GreenbergWilesFormula
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaloisCoh

theorem GlobalTheory.CompanionTheory.GaloisCoh.global_finite_of_poitouTate : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), μ.comp (toGS Ω _) = cycMod F Ω l r → Finite (TDual (ZMod (l ^ r)) M) → LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → ShaDual S Av μ ρ → Finite (H0 ρ) ∧ Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Finite (H0 (twDual μ ρ)) ∧ Finite (H1 (twDual μ ρ)) := by sorry
