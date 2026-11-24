-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_weilSourceAction_and_smooth
-- name    : GlobalTheory.T.exists_weilSourceAction_and_smooth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:46.058447+00:00
-- url     : https://prove2.me/theorems/42e3d98b-7269-46be-ad55-863d17b7d300
-- title:
--   T: exists weil Source Action and smooth
-- statement:
--   The T construction uses the exists weil Source Action and smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsWeilSourceActionAndSmoothStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsWeilSourceActionAndSmoothStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmoothStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_weilSourceAction_and_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∃ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ') ∧ ∀ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ' → IsSmoothRep ρ' := by sorry
