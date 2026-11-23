-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_ae_affine_ne
-- name    : GlobalTheory.FibLine.UnitaryInv.ae_affine_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:41.385448+00:00
-- url     : https://prove2.me/theorems/36b207b0-f771-4b24-95bb-51f2591dc8e0
-- title:
--   Unitary Inv: ae affine ne
-- statement:
--   The Unitary Inv construction uses the ae affine ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.UnitaryInv

theorem GlobalTheory.FibLine.UnitaryInv.ae_affine_ne (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) : ∀ᵐ x : ℂ, a + b * x ≠ 0 := by sorry
