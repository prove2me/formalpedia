-- Prove2me | Theorems.Thm_GlobalTheory_UpperUnitriangularMul_upperUnitriangular_mul
-- name    : GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:34:57.438135+00:00
-- url     : https://prove2.me/theorems/7451fc1c-1b6f-424e-bad0-ad795543d8c5
-- title:
--   Upper Unitriangular Mul: upper Unitriangular mul
-- statement:
--   The Upper Unitriangular Mul construction uses the upper Unitriangular mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UpperUnitriangularMul.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UpperUnitriangularMul.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperUnitriangularMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperUnitriangularMul
open Matrix

theorem GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by sorry
