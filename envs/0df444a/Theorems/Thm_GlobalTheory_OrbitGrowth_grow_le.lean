-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_grow_le
-- name    : GlobalTheory.OrbitGrowth.grow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:47.724146+00:00
-- url     : https://prove2.me/theorems/290a5322-6879-4f66-a3b8-5577b2489ef0
-- title:
--   Orbit Growth: grow le
-- statement:
--   The Orbit Growth construction uses the grow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L53-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.OrbitGrowth.grow_le {A : Subalgebra ℂ (Module.End ℂ M)} {W U : Submodule ℂ M} :
    grow A W ≤ U ↔ ∀ a ∈ A, ∀ x ∈ W, (a : M → M) x ∈ U := by sorry
