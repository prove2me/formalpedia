-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_psiInf_add
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.psiInf_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:59.159106+00:00
-- url     : https://prove2.me/theorems/680a090e-eb75-4c32-b556-463d14ee41d7
-- title:
--   Self Dual Inf: psi Inf add
-- statement:
--   The Self Dual Inf construction uses the psi Inf add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L398-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L398-L403

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SelfDualInf.psiInf_add (ψ : AddChar (AF F) ℂ) (x y : Ainf F) :
    psiInf F ψ (x + y) = psiInf F ψ x * psiInf F ψ y := by sorry
