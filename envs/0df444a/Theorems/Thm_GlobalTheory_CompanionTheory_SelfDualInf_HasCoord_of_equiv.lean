-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_of_equiv
-- name    : GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.of_equiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:06.198249+00:00
-- url     : https://prove2.me/theorems/98490282-3df2-4476-839b-e9c24abc6739
-- title:
--   Has Coord: of equiv
-- statement:
--   The Has Coord construction uses the of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean#L16-L20

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

theorem GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.of_equiv {V W : Type} [AddCommGroup V] [TopologicalSpace V] [AddCommGroup W]
    [TopologicalSpace W] (e : V ≃+ W) (h1 : Continuous e) (h2 : Continuous e.symm)
    (h : HasCoord W) : HasCoord V := by sorry
