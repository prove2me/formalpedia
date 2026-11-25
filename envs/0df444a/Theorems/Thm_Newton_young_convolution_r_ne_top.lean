-- Prove2me | Theorems.Thm_Newton_young_convolution_r_ne_top
-- name    : Newton.young_convolution_r_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:19.316614+00:00
-- url     : https://prove2.me/theorems/5304d084-1102-4d48-9119-f7c97d19421a
-- title:
--   Newton: young convolution r ne top
-- statement:
--   The Newton construction uses the young convolution r ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/InnerBound.lean#L962-L1599
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/InnerBound.lean#L962-L1599

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.young_convolution_r_ne_top
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by sorry
