-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_grow_good
-- name    : GlobalTheory.OrbitGrowth.grow_good
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:53.715478+00:00
-- url     : https://prove2.me/theorems/bb58bbfe-ce41-411c-85fb-738f6b03b9e6
-- title:
--   Orbit Growth: grow good
-- statement:
--   The Orbit Growth construction uses the grow good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L101-L110

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

theorem GlobalTheory.OrbitGrowth.grow_good {A B : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} (hW : W ≤ good B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : grow A W ≤ good B := by sorry
