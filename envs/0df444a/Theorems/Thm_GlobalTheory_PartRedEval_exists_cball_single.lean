-- Prove2me | Theorems.Thm_GlobalTheory_PartRedEval_exists_cball_single
-- name    : GlobalTheory.PartRedEval.exists_cball_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:20.16249+00:00
-- url     : https://prove2.me/theorems/d5ec6064-b152-4f6c-9cb7-1fb1969fc1dd
-- title:
--   Part Red Eval: exists cball single
-- statement:
--   The Part Red Eval construction uses the exists cball single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L59-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L59-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRedEval
open GlobalTheory.PartRed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
omit [Fintype R] [Fintype Q]

theorem GlobalTheory.PartRedEval.exists_cball_single {f : Matrix R Q k → ℂ} (hf : f ∈ SB (Matrix R Q k)) (e : R × Q) :
    ∃ s : kˣ, ∀ t ∈ cball s, ∀ x, f (x + Matrix.single e.1 e.2 t) = f x := by sorry
