-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_entry_truncatedLog_cleared_gaussian
-- name    : OAI.PiExponent.InterpolationMatrix.entry_truncatedLog_cleared_gaussian
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:47:29.380202+00:00
-- url     : https://prove2.me/theorems/922f6b18-bfda-41a8-9f45-ff48f8cec8a4
-- title:
--   Gaussian integrality of cleared truncated-logarithm interpolation entries
-- statement:
--   Fix $m$ coordinates and natural vectors $T,q,e$, integer numerators $p$, and assume $q_i\ne0$. Let $j,s,h$ be natural numbers and let $\alpha,\beta\in\mathbb N^m$ satisfy $\alpha_i\le e_i$. Set $r_i=2\mathrm i p_i/q_i$, $G_i=\ell_{T_i}(X)$, and $L_i=\operatorname{lcm}(1,\ldots,T_i)$, where $\ell_T$ is the polynomial truncation of $\log(1+X)$. The original interpolation entry $A_{j,s,\beta;h,\alpha}$ then satisfies
--
--   $$\left(\prod_iL_i^{e_i}\right)\frac{\prod_iq_i^{\alpha_i}}{\prod_iq_i^{\beta_i}}A_{j,s,\beta;h,\alpha}\in\mathbb Z[\mathrm i]\subset\mathbb C.$$
--
--   This clears the denominators of the logarithmic interpolation matrix at Gaussian rational centers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L74-L126

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Theorems.Thm_OAI_PiExponent_Arithmetic_shifted_truncation_product_coeff_gaussian

open OAI.PiExponent OAI.PiExponent.InterpolationMatrix
open scoped BigOperators

theorem OAI.PiExponent.InterpolationMatrix.entry_truncatedLog_cleared_gaussian {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      entry (fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ))
        (fun i => truncatedLog (T i)) j s β h α ∈ GaussianInt.toComplex.range := by
  sorry
