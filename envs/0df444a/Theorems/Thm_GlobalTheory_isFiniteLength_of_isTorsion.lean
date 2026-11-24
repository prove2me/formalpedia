-- Prove2me | Theorems.Thm_GlobalTheory_isFiniteLength_of_isTorsion
-- name    : GlobalTheory.isFiniteLength_of_isTorsion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:07.767768+00:00
-- url     : https://prove2.me/theorems/865c8202-2e00-4267-bdc3-93fa3afef1b5
-- title:
--   Global Theory: is Finite Length of is Torsion
-- statement:
--   The Global Theory construction uses the is Finite Length of is Torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthLocalizedModuleEqZeroOfNotAnnihilatorLe.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthLocalizedModuleEqZeroOfNotAnnihilatorLe.lean#L13-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain Function
open GlobalTheory
variable {R : Type*} [CommRing R]

theorem GlobalTheory.isFiniteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by sorry
