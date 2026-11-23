-- Prove2me | Theorems.Thm_GlobalTheory_SliceSchwartz_sliceRL_apply
-- name    : GlobalTheory.SliceSchwartz.sliceRL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:27.453094+00:00
-- url     : https://prove2.me/theorems/0d2757e0-bdb4-4941-a3a2-92536ca4b162
-- title:
--   Slice Schwartz: slice RL apply
-- statement:
--   The Slice Schwartz construction uses the slice RL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthElim.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthElim.lean#L44-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SliceSchwartz
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceSchwartz.sliceRL_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    sliceRL x f = sliceR f x := by sorry
