-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_exists_of_lpSum_twist_finite
-- name    : GlobalTheory.WeilDeligne.exists_of_lpSum_twist_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:05.780477+00:00
-- url     : https://prove2.me/theorems/9f4a8970-8a00-4728-b312-f8a9acf9e89e
-- title:
--   Weil Deligne: exists of lp Sum twist finite
-- statement:
--   The Weil Deligne construction uses the exists of lp Sum twist finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneInductionPrinciple.lean#L61-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneInductionPrinciple.lean#L61-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem GlobalTheory.WeilDeligne.exists_of_lpSum_twist_finite (S : WD h → Prop)
    (hsum : ∀ x y, S x → S y → S (x.lpSum y))
    (hfin : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = d → ∀ (ρ : Representation ℂ (Weil h) V), IsSmooth ρ →
      (∀ σ, End.IsSemisimple (ρ σ)) → ∃ y : WD h, S y ∧ ∀ σ, y.charPol σ = (ρ σ).charpoly := by sorry
