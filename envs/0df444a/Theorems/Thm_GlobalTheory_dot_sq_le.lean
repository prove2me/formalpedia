-- Prove2me | Theorems.Thm_GlobalTheory_dot_sq_le
-- name    : GlobalTheory.dot_sq_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:39.159368+00:00
-- url     : https://prove2.me/theorems/d6493d96-636d-40da-98cd-fffae554719a
-- title:
--   Global Theory: dot sq le
-- statement:
--   The Global Theory construction uses the dot sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SchurComplementBlockQuadraticLowerBound.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SchurComplementBlockQuadraticLowerBound.lean#L35-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.dot_sq_le (n : ℕ) (x v : Fin n → ℝ) : (x ⬝ᵥ v) ^ 2 ≤ (x ⬝ᵥ x) * (v ⬝ᵥ v) := by sorry
