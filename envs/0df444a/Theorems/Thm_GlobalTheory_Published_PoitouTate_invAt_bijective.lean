-- Prove2me | Theorems.Thm_GlobalTheory_Published_PoitouTate_invAt_bijective
-- name    : GlobalTheory.Published.PoitouTate.invAt_bijective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:56:30.301095+00:00
-- url     : https://prove2.me/theorems/3508f89a-d5a1-46e2-aabf-83d65cec1f08
-- title:
--   Poitou Tate: inv At bijective
-- statement:
--   The Poitou Tate construction uses the inv At bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean#L95-L99

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

theorem GlobalTheory.Published.PoitouTate.invAt_bijective (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) {ζ : Ω} {inv : InvFam F Ω l r}
    (h : IsLocalInvariants ζ inv) (v : S) (hv : IsPlaceOver (Av v) v.1) :
    Function.Bijective (invAt S Av μ hμ inv v) := by sorry
