-- Prove2me | Theorems.Thm_OAI_PiExponent_Arithmetic_shifted_truncation_product_coeff_gaussian
-- name    : OAI.PiExponent.Arithmetic.shifted_truncation_product_coeff_gaussian
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:19:38.861482+00:00
-- url     : https://prove2.me/theorems/6aa04075-729b-43a6-ab7e-004170285a5f
-- title:
--   Gaussian integrality of cleared shifted logarithm product coefficients
-- statement:
--   Let $S$ be a finite index set; let $T_i,q_i,e_i,d_i$ be natural numbers, $z_i\in\mathbb Z[\mathrm i]$, and $P\in\mathbb Z[\mathrm i][X]$. Assume $d_i\le e_i$ for $i\in S$. Write $L_i=\operatorname{lcm}(1,\ldots,T_i)$ and $\ell_{T_i}(X)$ for the order-$T_i$ polynomial truncation of $\log(1+X)$. For every natural $k$,
--
--   $$\left(\prod_{i\in S}L_i^{e_i}\right)[X^k]\left(P(X)\prod_{i\in S}(z_i+q_i\ell_{T_i}(X))^{d_i}\right)\in\mathbb Z[\mathrm i]\subset\mathbb C.$$
--
--   This is the exact coefficient-integrality statement used to clear denominators in the interpolation matrix entries.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Arithmetic.lean#L270-L279

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic

open OAI.PiExponent.Arithmetic

theorem OAI.PiExponent.Arithmetic.shifted_truncation_product_coeff_gaussian {ι : Type*} (s : Finset ι)
    (T q e d : ι → ℕ) (z : ι → GaussianInt) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i) (k : ℕ) :
    (∏ i ∈ s, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s,
        (Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
          PowerSeries.trunc (T i) (PowerSeries.log ℂ)) ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  sorry
