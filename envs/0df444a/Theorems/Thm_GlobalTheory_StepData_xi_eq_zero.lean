-- Prove2me | Theorems.Thm_GlobalTheory_StepData_xi_eq_zero
-- name    : GlobalTheory.StepData.xi_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:01.942084+00:00
-- url     : https://prove2.me/theorems/9e2608e6-8e55-4b98-94c2-5b75f27845ed
-- title:
--   Step Data: xi eq zero
-- statement:
--   The Step Data construction uses the xi eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L734-L738
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L734-L738

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
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
  (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
omit [BorelSpace k]

theorem GlobalTheory.StepData.xi_eq_zero {J : Subgroup (GL (n ⊕ Fin c) k)} (b : GL (n ⊕ Fin c) k) {h' : GL (n' ⊕ Fin (c + 1)) k}
    {h : GL (n ⊕ Fin c) k} (hh : DoubleCoset.mk (R k n c 1) J h ∉ idxAt ψ ν μ Φ J h') :
    xi ψ ν μ Φ J b h' h = 0 := by sorry
