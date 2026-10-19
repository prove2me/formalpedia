-- Prove2me | Theorems.Thm_Height_nonarchimedean_monic_root_le_coefficient_bound
-- name    : Height.nonarchimedean_monic_root_le_coefficient_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T23:43:07.925486+00:00
-- url     : https://prove2.me/theorems/d5d50268-1990-4ba5-97e8-2b02cd2e2872
-- title:
--   A nonarchimedean bound for roots of a monic polynomial
-- statement:
--   Let $K$ be a field and let $v:K\to\mathbb R$ be a real-valued nonarchimedean absolute value. Let $p\in K[T]$ be monic, and let $a\in K$ satisfy $p(a)=0$. If $B\ge1$ bounds $v(p_i)$ for every coefficient $p_i$ below the leading coefficient, then
--   $$v(a)\le B.$$
--   The proof uses the strict dominance of the monic leading term when $v(a)>B$. This bound contributes no extra factor at nonarchimedean places and is used for monic equations of normalized sections on the finite theta projective charts in the Mazur formalization.
-- source:
--   Standard nonarchimedean monic root estimate. Dominant-leading-term argument adapted from Mathlib, Valuation.Integers.isIntegral_iff_v_le_one, proof lines34–54: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Valuation/Integral.lean#L34-L54 . Standalone formulation developed for the original theta norm height comparison in MazurTheorem.

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Polynomial Finset
universe u

theorem Height.nonarchimedean_monic_root_le_coefficient_bound {K : Type u} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {p : Polynomial K} (hp : p.Monic) {a : K} (ha : p.IsRoot a)
    {B : ℝ} (hB : 1 ≤ B) (hc : ∀ i < p.natDegree, v (p.coeff i) ≤ B) : v a ≤ B := by sorry
