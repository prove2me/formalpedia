-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_round_abs_le_exp_pair
-- name    : OAI.AsymptoticallyMinimalLittlewood.round_abs_le_exp_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:32:41.87897+00:00
-- url     : https://prove2.me/theorems/6e595687-1842-424a-85c8-1af5dc41aeed
-- title:
--   Exponential bound for the size of a rounded quotient
-- statement:
--   For a real number $y$ let $\operatorname{round}(y)\in\mathbb{Z}$ be the nearest integer to $y$ (halves rounded up, i.e. $\operatorname{round}(y)=\lfloor y+\tfrac12\rfloor$). Let $x,d,t$ be real numbers with $d>0$, $t\ge 0$ and $td\ge 4$. Then
--
--   $$
--   \big|\operatorname{round}(x/d)\big|\le e^{\,tx-td/4}+e^{-tx-td/4}.
--   $$
--
--   The left side is the cost of quantizing $x$ to the grid $d\mathbb{Z}$; the inequality dominates it by exponential moments of $x$ that carry the damping factor $e^{-td/4}$. Applied to a randomly signed sum $x$, it turns moment generating function bounds into bounds on the expected quantization cost.
--
--   **Formalization Note** `round` is Mathlib's `round : ℝ → ℤ`, which rounds half-integers up; the proof only uses $|y-\operatorname{round}(y)|\le\tfrac12$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L61-L99

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.round_abs_le_exp_pair {x d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    |(round (x / d) : ℝ)| ≤
      Real.exp (t * x - t * d / 4) + Real.exp (-t * x - t * d / 4) := by sorry
