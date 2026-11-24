-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_trace
-- name    : GlobalTheory.CompanionTheory.AdeleCharLocal.exists_trace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:52.427274+00:00
-- url     : https://prove2.me/theorems/1dd759a0-96c3-46aa-8622-cf9cea45613a
-- title:
--   Adele Char Local: exists trace
-- statement:
--   The Adele Char Local construction uses the exists trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L142-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L142-L187

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

theorem GlobalTheory.CompanionTheory.AdeleCharLocal.exists_trace {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by sorry
