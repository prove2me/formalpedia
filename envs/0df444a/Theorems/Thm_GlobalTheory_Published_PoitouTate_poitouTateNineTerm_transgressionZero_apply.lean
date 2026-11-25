-- Prove2me | Theorems.Thm_GlobalTheory_Published_PoitouTate_poitouTateNineTerm_transgressionZero_apply
-- name    : GlobalTheory.Published.PoitouTate.poitouTateNineTerm_transgressionZero_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:04.564961+00:00
-- url     : https://prove2.me/theorems/560b8042-daaa-51e1-bb07-6c562e615472
-- title:
--   Poitou Tate: poitou Tate Nine Term transgression Zero apply
-- statement:
--   The Poitou Tate construction uses the poitou Tate Nine Term transgression Zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L130-L134

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
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

theorem GlobalTheory.Published.PoitouTate.poitouTateNineTerm_transgressionZero_apply (x : ∀ v : S, H0 (ρ.comp (locFam S Av v))) (y : H2 (twDual μ ρ)) :
    tr0 S Av μ j ρ x y = ∑ v : S, j v (cupH0H2TwistedDual μ ρ (locFam S Av v) (x v)
      (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y)) := by sorry
