-- Prove2me | Theorems.Thm_GlobalTheory_exists_flex_slope
-- name    : GlobalTheory.exists_flex_slope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:25.870668+00:00
-- url     : https://prove2.me/theorems/0e9d75cf-0a4b-46f4-a718-63d46d3dce94
-- title:
--   Global Theory: exists flex slope
-- statement:
--   The Global Theory construction uses the exists flex slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L126-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L126-L145

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

theorem GlobalTheory.exists_flex_slope {x y : F} (h : W.toAffine.Nonsingular x y) (h3 : W.Ψ₃.eval x = 0) :
    ∃ l : F, l * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ = 3 * x := by sorry
