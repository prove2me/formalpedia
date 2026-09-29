-- Prove2me | Theorems.Thm_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash
-- name    : ModularCurve.isBoundedAtImInfty_eisensteinTwoSlash_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/fce1f8c3-ef90-5820-b8b8-18b0a0a0cd38
-- title:
--   Boundedness at all cusps of p E₂(pz)-E₂(z)
-- statement:
--   Let $p$ be a natural number that is nonzero. Form the element [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) of $\mathrm{GL}_2(\mathbb{R})$: since $p \neq 0$ this is the upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$, regarded as invertible because its determinant $p \cdot 1$ is nonzero. Let $E_2 =$ `EisensteinSeries.E2` be the weight-two Eisenstein series on the upper half-plane, and let $\mid[2]$ denote the weight-two slash action of $\mathrm{GL}_2(\mathbb{R})$, so that $(f \mid[2] A)(z) = \det(A)\, (cz+d)^{-2} f(A \cdot z)$. Then the assertion is that for every $\gamma$ in $\mathrm{SL}_2(\mathbb{Z})$, the function obtained by slashing the difference $E_2 \mid[2] \begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix} - E_2$ by $\gamma$ in weight two is bounded at $i\infty$, i.e. `UpperHalfPlane.IsBoundedAtImInfty` holds for it: it is $O(1)$ along the filter in which $\operatorname{Im} z \to \infty$. Since the slash by the above diagonal matrix sends $E_2(z)$ to $p\,E_2(pz)$, the function in question is $\bigl(p\,E_2(p\,\cdot) - E_2\bigr)\mid[2]\gamma$.
--
--   The difference $p\,E_2(pz) - E_2(z)$ is, up to normalisation, the weight-two Eisenstein series of level $p$, and this statement is the boundedness-at-the-cusps condition needed for it to be a weight-two modular form on $\Gamma_0(p)$ rather than merely a quasi-modular form. It is used by [`ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff`](thm.html#ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash.lean

import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm

theorem ModularCurve.isBoundedAtImInfty_eisensteinTwoSlash_slash (p : ℕ) [NeZero p] : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, UpperHalfPlane.IsBoundedAtImInfty ((EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ) := by sorry
