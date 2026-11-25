-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_invariant_of_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.exists_invariant_of_mem_schwartzBruhat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:42.687444+00:00
-- url     : https://prove2.me/theorems/8b667e72-c9ab-4a8a-9ceb-40329e0f4d64
-- title:
--   Local Field: exists invariant of mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the exists invariant of mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L36-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L36-L80

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.exists_invariant_of_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    ∃ N M : ℤ, (∀ x, ∀ h ∈ valBall K N, f (x + h) = f x) ∧ ∀ x, f x ≠ 0 → x ∈ valBall K M := by sorry
