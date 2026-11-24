-- Prove2me | Theorems.Thm_GlobalTheory_PosOne_Unif_fixed_conjSub
-- name    : GlobalTheory.PosOne.Unif.fixed_conjSub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:12.649246+00:00
-- url     : https://prove2.me/theorems/d310d61b-0c44-468a-83e4-066a370fa1b0
-- title:
--   Unif: fixed conj Sub
-- statement:
--   The Unif construction uses the fixed conj Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExchangeToPositionOneUniformInLevel.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExchangeToPositionOneUniformInLevel.lean#L37-L45

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

theorem GlobalTheory.PosOne.Unif.fixed_conjSub {G A : Type} [Group G] [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ G A)
    (U : Subgroup G) (v : A) (hv : ∀ u ∈ U, σ u v = v) (g : G) :
    ∀ u ∈ conjSub U g, σ u (σ g v) = σ g v := by sorry
