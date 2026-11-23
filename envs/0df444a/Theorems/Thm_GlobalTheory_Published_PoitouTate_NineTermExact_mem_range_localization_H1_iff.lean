-- Prove2me | Theorems.Thm_GlobalTheory_Published_PoitouTate_NineTermExact_mem_range_localization_H1_iff
-- name    : GlobalTheory.Published.PoitouTate.NineTermExact.mem_range_localization_H1_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:41.883022+00:00
-- url     : https://prove2.me/theorems/1ac60357-8b06-4965-a46a-fadc5ddc039f
-- title:
--   Nine Term Exact: mem range localization H1 iff
-- statement:
--   The Nine Term Exact construction uses the mem range localization H1 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L179-L186

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
open GlobalTheory.Published.PoitouTate
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
variable (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
variable {S Av μ j ρ}

theorem GlobalTheory.Published.PoitouTate.NineTermExact.mem_range_localization_H1_iff {hρ : ContAction ρ} (h : NineTermExact S Av μ j ρ hρ)
    (x : ∀ v : S, H1 (ρ.comp (locFam S Av v))) :
    x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
      ∑ v : S, j v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))
        (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0 := by sorry
