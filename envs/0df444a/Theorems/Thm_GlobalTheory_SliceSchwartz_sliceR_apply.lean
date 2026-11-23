-- Prove2me | Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- name    : GlobalTheory.SliceSchwartz.sliceR_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:39.48554+00:00
-- url     : https://prove2.me/theorems/864f21c2-1399-4b66-9718-4e623593665c
-- title:
--   Slice Schwartz: slice R apply
-- statement:
--   The Slice Schwartz construction uses the slice R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthElim.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthElim.lean#L37-L38

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

theorem GlobalTheory.SliceSchwartz.sliceR_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V)
    (y : κ' → V) : sliceR f x y = f (Sum.elim x y) := by sorry

attribute [defeq] GlobalTheory.SliceSchwartz.sliceR_apply
