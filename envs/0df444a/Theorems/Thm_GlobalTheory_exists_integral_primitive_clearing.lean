-- Prove2me | Theorems.Thm_GlobalTheory_exists_integral_primitive_clearing
-- name    : GlobalTheory.exists_integral_primitive_clearing
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:29.423906+00:00
-- url     : https://prove2.me/theorems/18c8890a-7086-4db8-a629-b990b6314fdd
-- title:
--   Global Theory: exists integral primitive clearing
-- statement:
--   The Global Theory construction uses the exists integral primitive clearing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L7-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L7-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.exists_integral_primitive_clearing : ∀ (K : Type) [Field K] [NumberField K], ∃ θ : K, IsIntegral ℤ θ ∧ 0 < (minpoly ℤ θ).natDegree ∧ ((minpoly ℤ θ).map (Int.castRingHom ℚ)).Separable ∧ ∀ s : K, ∃ N : ℕ, 0 < N ∧ (N : K) * s ∈ Algebra.adjoin ℤ ({θ} : Set K) := by sorry
