-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PoitouTateGlue_range_localization_eq_annihilator
-- name    : GlobalTheory.CompanionTheory.PoitouTateGlue.range_localization_eq_annihilator
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:03.125815+00:00
-- url     : https://prove2.me/theorems/73feda97-91ef-4912-97e2-105a54218727
-- title:
--   Poitou Tate Glue: range localization eq annihilator
-- statement:
--   The Poitou Tate Glue construction uses the range localization eq annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichDualityH1.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichDualityH1.lean#L8-L37

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichDualityH1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PoitouTateGlue

theorem GlobalTheory.CompanionTheory.PoitouTateGlue.range_localization_eq_annihilator (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ)
    (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
    (h : NineTermExact S Av μ j ρ hρ) :
    LinearMap.range (loc1 S Av ρ) =
      ⨅ y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)), LinearMap.ker (sumPair S Av μ j ρ hρ y) := by sorry
