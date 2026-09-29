-- Prove2me | Theorems.Thm_ModularCurve_eisensteinTwoSlash_slash_eq_self
-- name    : ModularCurve.eisensteinTwoSlash_slash_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/d763d593-5161-510e-8932-8a4c32468857
-- title:
--   Γ₀(p)-invariance of p E₂(pz)-E₂(z)
-- statement:
--   Let $p$ be a natural number with $p \neq 0$. Write $\mid[k]$ for the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$ on functions $\mathbb{H} \to \mathbb{C}$, and let [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) denote the element of $\mathrm{GL}_2(\mathbb{R})$ which is the identity when $p = 0$ and otherwise is the invertible upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$, i.e.\ $\mathrm{diag}(p,1)$ in the case at hand. Set $g = E_2 \mid[2] \mathrm{diag}(p,1) - E_2$, where $E_2$ is Mathlib's weight-two Eisenstein series `EisensteinSeries.E2` on the upper half plane. The assertion is that for every element $\gamma$ of the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained as the image of $\Gamma_0(p) \leq \mathrm{SL}_2(\mathbb{Z})$ under the canonical map $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{GL}_2(\mathbb{R})$, one has $g \mid[2] \gamma = g$. Thus the difference $g$, classically $p\,E_2(pz) - E_2(z)$ up to normalisation, is weakly modular of weight $2$ for $\Gamma_0(p)$; no growth or holomorphy condition is part of the conclusion.
--
--   This is the weak modularity of the level-$p$ weight-two Eisenstein combination $p\,E_2(pz)-E_2(z)$ for $\Gamma_0(p)$, the quasi-modularity defects of $E_2$ at $\gamma$ and at its conjugate cancelling exactly. It is used in the construction of a weight-two modular form of level $p$ with prescribed $q$-expansion coefficients, in [`ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff`](thm.html#ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinTwoSlash_slash_eq_self.lean

import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm

theorem ModularCurve.eisensteinTwoSlash_slash_eq_self (p : ℕ) [NeZero p] : ∀ γ ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ = EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2 := by sorry
