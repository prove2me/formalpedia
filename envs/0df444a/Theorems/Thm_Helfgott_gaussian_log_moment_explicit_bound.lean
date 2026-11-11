-- Prove2me | Theorems.Thm_Helfgott_gaussian_log_moment_explicit_bound
-- name    : Helfgott.gaussian_log_moment_explicit_bound
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T00:45:20.893682+00:00
-- url     : https://prove2.me/theorems/b1fd26ad-c9a4-4c88-ae03-e55833a3dc21
-- title:
--   Explicit Gaussian logarithmic-moment bounds for minor arcs
-- statement:
--   Let $0\le a\le1$ and put
--
--   $$I(a)=\int_a^1 t^2e^{-t^2/2}(-\log t)\,dt.$$
--
--   Then
--
--   $$I(a)\le0.093426,\qquad \frac{I(a)}{\sqrt{\pi/2}}\le0.07455.$$
--
--   The integral is finite at $a=0$, because $t^2\log t$ extends continuously to zero. Both endpoints $a=0$ and $a=1$ are included.
--
--   For Helfgott's smoothing $\varphi(t)=t^2e^{-t^2/2}$ and $K>1$, the choice $a=1/K$ supplies the logarithmic moment $C_{\varphi,2,K}$. The normalized inequality, divided by the positive number $\log K$, is the numerical input in equation (7.31) of the minor-arc argument. This result does not assert the remaining pointwise, sieve, or total minor-arc estimates.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, Section 7.3, the displayed bound C_{phi,2,K} <= 0.093426 immediately preceding equation (7.31), and equation (7.31) itself. https://arxiv.org/html/1312.7748v2 . The formalization proves the published upper bounds uniformly for every lower integration endpoint in [0,1].

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MeasureTheory Finset
open scoped BigOperators

theorem Helfgott.gaussian_log_moment_explicit_bound (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ t in a..1, t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) ≤
      (46713 / 500000 : ℝ) ∧
    (∫ t in a..1, t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) /
      Real.sqrt (Real.pi / 2) ≤ (1491 / 20000 : ℝ) := by sorry
