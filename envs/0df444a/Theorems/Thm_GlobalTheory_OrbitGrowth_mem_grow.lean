-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_mem_grow
-- name    : GlobalTheory.OrbitGrowth.mem_grow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:00.248578+00:00
-- url     : https://prove2.me/theorems/6043be65-8cdc-4844-ae7f-34200de7fc15
-- title:
--   Orbit Growth: mem grow
-- statement:
--   The Orbit Growth construction uses the mem grow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L61-L63

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

theorem GlobalTheory.OrbitGrowth.mem_grow {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ W) : (a : M → M) x ∈ grow A W := by sorry
