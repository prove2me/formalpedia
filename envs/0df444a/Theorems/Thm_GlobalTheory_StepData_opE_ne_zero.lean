-- Prove2me | Theorems.Thm_GlobalTheory_StepData_opE_ne_zero
-- name    : GlobalTheory.StepData.opE_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:51:08.418927+00:00
-- url     : https://prove2.me/theorems/2307fb16-b551-44d0-b13b-6f56dd9aeecb
-- title:
--   Step Data: op E ne zero
-- statement:
--   The Step Data construction uses the op E ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1200-L1226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1200-L1226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
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
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.StepData.opE_ne_zero [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h01 : ∀ x, Φ x ≠ 0 → Φ x = 1 ∧ IntM x) {x₀ : Matrix n n' k} {e₀} (he : Φ (affPt p x₀ e₀) ≠ 0) :
    opE ψ ν p Φ x₀ ≠ 0 := by sorry
