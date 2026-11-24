-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_grow_inv
-- name    : GlobalTheory.OrbitGrowth.grow_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:10.011801+00:00
-- url     : https://prove2.me/theorems/4f70dafe-66a6-4123-8dae-b1c6e8b50f85
-- title:
--   Orbit Growth: grow inv
-- statement:
--   The Orbit Growth construction uses the grow inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L70-L76

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

theorem GlobalTheory.OrbitGrowth.grow_inv {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ grow A W) : (a : M → M) x ∈ grow A W := by sorry
