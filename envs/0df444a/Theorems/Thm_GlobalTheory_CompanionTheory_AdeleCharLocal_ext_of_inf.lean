-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_ext_of_inf
-- name    : GlobalTheory.CompanionTheory.AdeleCharLocal.ext_of_inf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:15.074594+00:00
-- url     : https://prove2.me/theorems/19e9c9b9-2ade-410a-854b-8d15e8052c2c
-- title:
--   Adele Char Local: ext of inf
-- statement:
--   The Adele Char Local construction uses the ext of inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L64-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L64-L85

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.AdeleCharLocal.ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by sorry
