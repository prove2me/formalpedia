-- Prove2me | Theorems.Thm_GlobalTheory_Published_PoitouTateTotallyComplex_annihilators
-- name    : GlobalTheory.Published.PoitouTateTotallyComplex.annihilators
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:54.152447+00:00
-- url     : https://prove2.me/theorems/e0ae3988-a2ad-4608-a30c-d7fd1892ac0a
-- title:
--   Poitou Tate Totally Complex: annihilators
-- statement:
--   The Poitou Tate Totally Complex construction uses the annihilators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L305-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L305-L340

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open PoitouTate

theorem GlobalTheory.Published.PoitouTateTotallyComplex.annihilators (h : PoitouTateTotallyComplex)
    (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    (∀ x : H2 (charRep μ), ∑ v : S, invAt S Av μ hμ inv v
      (resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) x) = 0) ∧
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      (∀ x : ∀ v : S, H1 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v))
            (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0) ∧
      (∀ x : ∀ v : S, H2 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc2 S Av ρ) ↔ ∀ y : H0 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cup20 μ ρ (locFam S Av v) (x v)
            (resH0 (twDual μ ρ) (locFam S Av v) y)) = 0) ∧
      Finite (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
      Finite (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) ∧
      Nat.card (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) =
        Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) := by sorry
