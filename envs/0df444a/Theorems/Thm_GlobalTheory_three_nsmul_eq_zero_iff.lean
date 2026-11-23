-- Prove2me | Theorems.Thm_GlobalTheory_three_nsmul_eq_zero_iff
-- name    : GlobalTheory.three_nsmul_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:29.413069+00:00
-- url     : https://prove2.me/theorems/d1fb9f00-9d89-4767-87f2-847a414153fb
-- title:
--   Global Theory: three nsmul eq zero iff
-- statement:
--   The Global Theory construction uses the three nsmul eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L147-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L147-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {F : Type*} [Field F] {W : WeierstrassCurve F}

theorem GlobalTheory.three_nsmul_eq_zero_iff [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y) :
    3 • Point.some x y h = 0 ↔ W.Ψ₃.eval x = 0 := by sorry
