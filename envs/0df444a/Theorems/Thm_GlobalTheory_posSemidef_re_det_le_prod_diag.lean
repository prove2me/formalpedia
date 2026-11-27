-- Prove2me | Theorems.Thm_GlobalTheory_posSemidef_re_det_le_prod_diag
-- name    : GlobalTheory.posSemidef_re_det_le_prod_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:49:29.58782+00:00
-- url     : https://prove2.me/theorems/f21da372-19e5-48c2-897a-97e5ccef4acc
-- title:
--   Global Theory: pos Semidef re det le prod diag
-- statement:
--   The Global Theory construction uses the pos Semidef re det le prod diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L60-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.posSemidef_re_det_le_prod_diag {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i) := by sorry
