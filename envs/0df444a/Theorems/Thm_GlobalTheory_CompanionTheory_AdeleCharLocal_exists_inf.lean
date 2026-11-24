-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_inf
-- name    : GlobalTheory.CompanionTheory.AdeleCharLocal.exists_inf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:23:42.451288+00:00
-- url     : https://prove2.me/theorems/87f461ea-7a7a-4768-b1e4-ec5f44933e53
-- title:
--   Adele Char Local: exists inf
-- statement:
--   The Adele Char Local construction uses the exists inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L208-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/SelfDualLatticeFiltrationCharacter.lean#L208-L253

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

theorem GlobalTheory.CompanionTheory.AdeleCharLocal.exists_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (w : InfinitePlace F) :
    ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by sorry
