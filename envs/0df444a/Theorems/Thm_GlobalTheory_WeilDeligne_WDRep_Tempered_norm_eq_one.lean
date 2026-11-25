-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_Tempered_norm_eq_one
-- name    : GlobalTheory.WeilDeligne.WDRep.Tempered.norm_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:14.821859+00:00
-- url     : https://prove2.me/theorems/4f660aec-15ba-4c5f-bb1c-e5aa2bb9fa87
-- title:
--   Tempered: norm eq one
-- statement:
--   The Tempered construction uses the norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L595-L611
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L595-L611

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem GlobalTheory.WeilDeligne.WDRep.Tempered.norm_eq_one {a : WDRep h V} (ha : a.Tempered)
    (hN : a.N = 0) {φ : Weil h} (hφ : deg φ = 1) : absSpace (a.ρ φ) 1 = ⊤ := by sorry
