-- Prove2me | Theorems.Thm_GlobalTheory_StepData_volN_Cgrp
-- name    : GlobalTheory.StepData.volN_Cgrp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:06.957918+00:00
-- url     : https://prove2.me/theorems/36bd4ace-79a2-4717-b469-4490e3fa8453
-- title:
--   Step Data: vol N Cgrp
-- statement:
--   The Step Data construction uses the vol N Cgrp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L749-L757
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L749-L757

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

theorem GlobalTheory.StepData.volN_Cgrp [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k))) (h : GL (n ⊕ Fin c) k) :
    volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) ≠ 0 ∧ volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) ≠ ⊤ := by sorry
