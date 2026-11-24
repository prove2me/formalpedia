-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_mem_fractionalIdeal_place_le
-- name    : GlobalTheory.exists_ne_zero_mem_fractionalIdeal_place_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:10.59431+00:00
-- url     : https://prove2.me/theorems/22932c44-e845-4e38-b5a4-676a04f0646b
-- title:
--   Global Theory: exists ne zero mem fractional Ideal place le
-- statement:
--   The Global Theory construction uses the exists ne zero mem fractional Ideal place le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroMemFractionalIdealNormSqLe.lean#L14-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroMemFractionalIdealNormSqLe.lean#L14-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal
variable (K : Type*) [Field K] [NumberField K]
open scoped Classical

theorem GlobalTheory.exists_ne_zero_mem_fractionalIdeal_place_le (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (g : InfinitePlace K → ℝ≥0) (h : minkowskiBound K I ≤ volume (convexBodyLT K g)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a ≤ g w := by sorry
