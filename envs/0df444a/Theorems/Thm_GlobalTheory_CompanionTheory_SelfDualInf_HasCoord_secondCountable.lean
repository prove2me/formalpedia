-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_secondCountable
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.secondCountable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:43.078806+00:00
-- url     : https://prove2.me/theorems/a8e9ce32-df20-4eaf-afac-e0caf38766bd
-- title:
--   Has Coord: second Countable
-- statement:
--   The Has Coord construction uses the second Countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L56-L59

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

theorem GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.secondCountable {V : Type} [AddCommGroup V] [TopologicalSpace V]
    (h : HasCoord V) : SecondCountableTopology V := by sorry
