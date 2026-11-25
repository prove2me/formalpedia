-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_main
-- name    : GlobalTheory.OrbitGrowth.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:41.419785+00:00
-- url     : https://prove2.me/theorems/dcb043ea-999d-4e5a-9810-905b6cddb965
-- title:
--   Orbit Growth: main
-- statement:
--   The Orbit Growth construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L112-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L112-L143

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

theorem GlobalTheory.OrbitGrowth.main : ∀ (M : Type) [inst : AddCommGroup M] [inst_1 : Module ℂ M] (ι : Type) [Finite ι]
    (A : ι → Subalgebra ℂ (Module.End ℂ M)),
    (∀ (i j : ι), i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ (m : M),
    (∀ (i : ι), FiniteDimensional ℂ ↥(Submodule.span ℂ {x : M | ∃ a ∈ A i, x = (a : M → M) m})) →
    ∃ (W : Submodule ℂ M), FiniteDimensional ℂ ↥W ∧ m ∈ W ∧
      ∀ (i : ι), ∀ a ∈ A i, ∀ x ∈ W, (a : M → M) x ∈ W := by sorry
