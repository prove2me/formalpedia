-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_half
-- name    : GlobalTheory.TwoStepUnipotent.st_half
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:38.311461+00:00
-- url     : https://prove2.me/theorems/addbc039-8ec8-4dbb-a786-e53d3cfa1a9c
-- title:
--   Two Step Unipotent: st half
-- statement:
--   The Two Step Unipotent construction uses the st half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L18-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}

theorem GlobalTheory.TwoStepUnipotent.st_half (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) : st h = h := by sorry
