-- Prove2me | Theorems.Thm_NarrowDNF_WidthBound_ceil_width_le_exp
-- name    : NarrowDNF.WidthBound.ceil_width_le_exp
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:58.520188+00:00
-- url     : https://prove2.me/theorems/d002c2dd-6915-4ed3-9b93-71eb3f9642d8
-- title:
--   Absorbing an integer ceiling and width prefactor into an exponential
-- statement:
--   For every $\varepsilon>0$, $a\ge0$, and integer $d\ge0$,
--   $$
--   \left\lceil\frac{4\,2^d e^a}{\varepsilon}\right\rceil
--   \le\exp\left(\frac4\varepsilon+d+a\right).
--   $$
--   The ceiling is the nonnegative-integer ceiling, viewed as a real number. This estimate preserves the explicit width chosen by the certificate construction while replacing its prefactor, power of two, and rounding term by a single exponential. It does not require an upper bound on $\varepsilon$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L41-L63

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound
noncomputable section
open NarrowDNF
open NarrowDNF.WidthBound

theorem NarrowDNF.WidthBound.ceil_width_le_exp {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (d : ℕ) :
    (Nat.ceil (4 * (2 : ℝ)^d * Real.exp a / ε) : ℝ) ≤
      Real.exp (4 / ε + (d : ℝ) + a) := by sorry
