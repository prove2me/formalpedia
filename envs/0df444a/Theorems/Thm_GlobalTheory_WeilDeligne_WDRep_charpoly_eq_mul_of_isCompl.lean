-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_charpoly_eq_mul_of_isCompl
-- name    : GlobalTheory.WeilDeligne.WDRep.charpoly_eq_mul_of_isCompl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:54.382328+00:00
-- url     : https://prove2.me/theorems/2c5339a0-9dc0-42a4-b05f-6b6e0e92b2a7
-- title:
--   WDRep: charpoly eq mul of is Compl
-- statement:
--   The WDRep construction uses the charpoly eq mul of is Compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneInductionPrinciple.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneInductionPrinciple.lean#L28-L38

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

theorem GlobalTheory.WeilDeligne.WDRep.charpoly_eq_mul_of_isCompl {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (U U' : Submodule ℂ V)
    (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (hU' : ∀ σ, ∀ v ∈ U', a.ρ σ v ∈ U') (hc : IsCompl U U')
    (σ : Weil h) :
    (a.ρ σ).charpoly = ((a.resZero U hU).ρ σ).charpoly * ((a.resZero U' hU').ρ σ).charpoly := by sorry
