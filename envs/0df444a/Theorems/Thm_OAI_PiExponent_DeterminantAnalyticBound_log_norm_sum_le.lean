-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le
-- name    : OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T06:19:52.058069+00:00
-- url     : https://prove2.me/theorems/10a08e49-5f89-4055-a254-59882a447190
-- title:
--   Logarithmic bound for a finite exponential sum
-- statement:
--   Let $\Omega$ be a finite index type, $M>0$ a natural number, $H,Q>0$ real numbers, $E\in\mathbb R$, and $t:\Omega\to\mathbb C$. Suppose $|\Omega|\le Q^M$, $\delta=\sum_{x\in\Omega}t(x)\ne0$, and $|t(x)|\le\exp(MHE)$ for every $x$. Then
--
--   $$\frac{\log|\delta|}{MH}\le E+\frac{\log Q}{H}.$$
--
--   The estimate separates the exponential size of each summand from the number of summands. It is used in the analytic determinant estimates in OpenAI's PiExponent proof. No positivity hypothesis on $E$ and no hypothesis $Q>1$ is imposed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean#L105-L130

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix

open scoped BigOperators

theorem OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le {Ω : Type*} [Fintype Ω]
    (term : Ω → ℂ) (delta : ℂ) {M : ℕ} {H Q E : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hQ : 0 < Q)
    (hcard : (Fintype.card Ω : ℝ) ≤ Q ^ M)
    (hexpansion : delta = ∑ x, term x) (hne : delta ≠ 0)
    (hterm : ∀ x, ‖term x‖ ≤ Real.exp ((M : ℝ) * H * E)) :
    Real.log ‖delta‖ / ((M : ℝ) * H) ≤ E + Real.log Q / H := by sorry
