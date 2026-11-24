-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_ainf
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.hasCoord_ainf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:38:09.590797+00:00
-- url     : https://prove2.me/theorems/da45a5bc-5a51-477c-a125-18065ff01d4c
-- title:
--   Self Dual Inf: has Coord ainf
-- statement:
--   The Self Dual Inf construction uses the has Coord ainf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L387-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L387-L396

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

theorem GlobalTheory.CompanionTheory.SelfDualInf.hasCoord_ainf (hF : IsTotallyReal F) : HasCoord (Ainf F) := by sorry
