-- Prove2me | Theorems.Thm_GlobalTheory_laurent_vector_normalise
-- name    : GlobalTheory.laurent_vector_normalise
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:00.732905+00:00
-- url     : https://prove2.me/theorems/0b552e5a-ff68-4049-aa9e-37a3fc8bd09a
-- title:
--   Global Theory: laurent vector normalise
-- statement:
--   The Global Theory construction uses the laurent vector normalise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentDegenerationFirstOrderKernel.lean#L83-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentDegenerationFirstOrderKernel.lean#L83-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.laurent_vector_normalise (k : Type) [Field k] (a : ℕ) (y : Fin a → HahnSeries ℤ k)
    (hy : y ≠ 0) : ∃ (f : HahnSeries ℤ k) (c0 : Fin a), f * y c0 = 1 ∧
      ∀ c, (f * y c).coeff (-1) = 0 := by sorry
