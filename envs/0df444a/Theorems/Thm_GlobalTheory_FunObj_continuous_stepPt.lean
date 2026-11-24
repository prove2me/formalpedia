-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_continuous_stepPt
-- name    : GlobalTheory.FunObj.continuous_stepPt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:59.189316+00:00
-- url     : https://prove2.me/theorems/7376b4be-5e65-4a49-9675-0b4bd42e3010
-- title:
--   Fun Obj: continuous step Pt
-- statement:
--   The Fun Obj construction uses the continuous step Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L29-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

theorem GlobalTheory.FunObj.continuous_stepPt {n n' : Type*} {c : ℕ} (x₀ : Matrix n n' k) :
    Continuous fun e : StepVar n c n' → k => stepPt x₀ e := by sorry
