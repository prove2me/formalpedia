-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_grow_fd
-- name    : GlobalTheory.OrbitGrowth.grow_fd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:11.261957+00:00
-- url     : https://prove2.me/theorems/3049b2ae-c819-47eb-8a6d-ee4189c57e71
-- title:
--   Orbit Growth: grow fd
-- statement:
--   The Orbit Growth construction uses the grow fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L87-L99

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

theorem GlobalTheory.OrbitGrowth.grow_fd {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} [FiniteDimensional ℂ W]
    (hW : W ≤ good A) : FiniteDimensional ℂ (grow A W) := by sorry
