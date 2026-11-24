-- Prove2me | Theorems.Thm_GlobalTheory_PosOne_Unif_isOpen_conjSub
-- name    : GlobalTheory.PosOne.Unif.isOpen_conjSub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:21.939991+00:00
-- url     : https://prove2.me/theorems/ef716531-15f0-40c9-ba59-0556ece9d0c6
-- title:
--   Unif: is Open conj Sub
-- statement:
--   The Unif construction uses the is Open conj Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExchangeToPositionOneUniformInLevel.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExchangeToPositionOneUniformInLevel.lean#L30-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneUniformInLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.Unif

theorem GlobalTheory.PosOne.Unif.isOpen_conjSub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (g : G) : IsOpen (conjSub U g : Set G) := by sorry
