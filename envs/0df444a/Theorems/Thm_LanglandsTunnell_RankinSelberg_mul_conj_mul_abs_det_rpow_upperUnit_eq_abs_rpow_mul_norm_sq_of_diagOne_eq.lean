-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq
-- name    : LanglandsTunnell.RankinSelberg.mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/115f5835-5dd7-597a-8c5e-1660de72c687
-- title:
--   Torus profile of a Whittaker function twisted by |det|^{-e}
-- statement:
--   Fix a function $W_A$ on $\mathrm{GL}_2(\mathbb{R})$ with complex values, a function $\chi$ on the units $\mathbb{R}^\times$ with complex values, a function $W_r$ on $\mathbb{R}$ with complex values, and a real exponent $e$. Assume: (i) $\|\chi(z)\| = |z|^{e}$ (real power) for every unit $z$; (ii) $W_A$ transforms under the centre by $\chi$, i.e. $W_A(\mathrm{scalar}(z)\,h) = \chi(z)\,W_A(h)$ for every unit $z$ and every $h \in \mathrm{GL}_2(\mathbb{R})$, where $\mathrm{scalar}(z)$ is the scalar matrix $z\cdot I_2$; and (iii) the values of $W_A$ on the torus elements `diagOne t`, the invertible diagonal matrix $\mathrm{diag}(t,1)$ for $t$ a unit, are given by $W_A(\mathrm{diag}(t,1)) = W_r(t)$. The conclusion is that for all reals $a_1 \neq 0$ and $a_2 > 0$, writing $g =$ `upperUnit a₁ 0 a₂` for the invertible matrix $\begin{pmatrix} a_1 & 0 \\ 0 & a_2\end{pmatrix}$, one has
--   $$W_A(g)\cdot\bigl(\overline{W_A(g)}\cdot |a_1 a_2|^{-e}\bigr) = |a_1/a_2|^{-e}\,\|W_r(a_1/a_2)\|^{2},$$
--   the right-hand side being the real number so formed, viewed in $\mathbb{C}$.
--
--   This is the elementary normalisation computation showing that, on the diagonal torus, the product of an archimedean Whittaker-type function with central character of modulus $|z|^e$ against its conjugate twisted by $|\det|^{-e}$ depends only on the ratio of the diagonal entries, yielding the torus profile $y \mapsto |y|^{-e}\|W_r(y)\|^2$. It feeds the construction of Rankin–Selberg test data over $\mathbb{Q}$, being used by [`LanglandsTunnell.RankinSelberg.exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.RankinSelberg.mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq
    (WA : GL (Fin 2) ℝ → ℂ) (χ : ℝˣ → ℂ) (Wr : ℝ → ℂ) (e : ℝ)
    (hχ : ∀ z : ℝˣ, ‖χ z‖ = |(z : ℝ)| ^ e)
    (hZ : ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ), WA (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = χ z * WA h)
    (hdiag : ∀ t : ℝˣ, WA (diagOne t) = Wr (t : ℝ)) :
    ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') *
          ((starRingEnd ℂ) (WA (upperUnit a₁ 0 a₂ h₁ h₂.ne')) * (((|a₁ * a₂| ^ (-e) : ℝ) : ℝ) : ℂ)) =
        (((|a₁ / a₂| ^ (-e) * ‖Wr (a₁ / a₂)‖ ^ 2 : ℝ) : ℝ) : ℂ) := by sorry
