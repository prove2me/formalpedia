-- Prove2me | Theorems.Thm_GlobalTheory_StepData_xi_eq_zero_iff
-- name    : GlobalTheory.StepData.xi_eq_zero_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:49.273128+00:00
-- url     : https://prove2.me/theorems/090547ce-5ebd-4d35-8696-b10df8715967
-- title:
--   Step Data: xi eq zero iff
-- statement:
--   The Step Data construction uses the xi eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L764-L769
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L764-L769

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

theorem GlobalTheory.StepData.xi_eq_zero_iff [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)}
    (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k)))
    (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    xi ψ ν μ Φ J b h' h = 0 ↔ flat ψ ν μ Φ h' h = 0 := by sorry
