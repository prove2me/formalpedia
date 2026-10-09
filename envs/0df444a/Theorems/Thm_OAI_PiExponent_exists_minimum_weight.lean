-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_minimum_weight
-- name    : OAI.PiExponent.exists_minimum_weight
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T10:12:08.779826+00:00
-- url     : https://prove2.me/theorems/30d83fa5-620d-4059-a909-387ac02d2401
-- title:
--   A nonempty finite family of weights has an attained minimum
-- statement:
--   Let $m\geq1$ be an integer and let $w_0,\ldots,w_{m-1}\in\mathbb R$. If $X\in\mathbb R$ satisfies $X<w_i$ for every $0\leq i<m$, then there exists $w_\ast\in\mathbb R$ such that
--
--   $$X<w_\ast,\qquad w_\ast\leq w_i\quad(0\leq i<m),\qquad w_\ast=w_j\quad\text{for some }0\leq j<m.$$
--
--   This attained minimum provides a common lower bound for a nonempty finite family of weights, while retaining the strict bound above the prescribed scale $X$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightErrorMargin.lean#L51-L59

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

theorem OAI.PiExponent.exists_minimum_weight
    (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℝ) (X : ℝ)
    (hX : ∀ i, X < w i) :
    ∃ wstar : ℝ, X < wstar ∧ (∀ i, wstar ≤ w i) ∧
      ∃ i, wstar = w i := by sorry
