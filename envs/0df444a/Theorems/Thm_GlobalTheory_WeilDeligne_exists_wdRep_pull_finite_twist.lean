-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_exists_wdRep_pull_finite_twist
-- name    : GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:18.927827+00:00
-- url     : https://prove2.me/theorems/d4a895bc-b8e6-571a-b071-132a110fb7ac
-- title:
--   Weil Deligne: exists wd Rep pull finite twist
-- statement:
--   The Weil Deligne construction uses the exists wd Rep pull finite twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneOfFiniteImage.lean#L9-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneOfFiniteImage.lean#L9-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneOfFiniteImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type)
      [Group G] [Finite G] (π : Weil h →* G),
      IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ)
      (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ →
      ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by sorry
