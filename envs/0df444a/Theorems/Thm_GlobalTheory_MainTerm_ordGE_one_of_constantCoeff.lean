-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_ordGE_one_of_constantCoeff
-- name    : GlobalTheory.MainTerm.ordGE_one_of_constantCoeff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:59.189803+00:00
-- url     : https://prove2.me/theorems/0209b7d4-8165-4f7b-8177-8d3120586666
-- title:
--   Main Term: ord GE one of constant Coeff
-- statement:
--   The Main Term construction uses the ord GE one of constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L32-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)
noncomputable section
open GlobalTheory GlobalTheory.MainTerm

theorem GlobalTheory.MainTerm.ordGE_one_of_constantCoeff {C : Type} [Field C] {ι : Type} {F : MvPowerSeries ι C}
    (h : MvPowerSeries.constantCoeff F = 0) : OrdGE 1 F := by sorry
