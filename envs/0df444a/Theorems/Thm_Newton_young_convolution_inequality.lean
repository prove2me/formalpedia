-- Prove2me | Theorems.Thm_Newton_young_convolution_inequality
-- name    : Newton.young_convolution_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:43:25.246797+00:00
-- url     : https://prove2.me/theorems/6b009f15-ab65-428f-9ef8-07265fdb1837
-- title:
--   Newton: young convolution inequality
-- statement:
--   The Newton construction uses the young convolution inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Basic.lean#L11-L270
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Basic.lean#L11-L270

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
import Definitions.Def_Newton_Analysis_Convolution_Basic
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.young_convolution_inequality
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by sorry
