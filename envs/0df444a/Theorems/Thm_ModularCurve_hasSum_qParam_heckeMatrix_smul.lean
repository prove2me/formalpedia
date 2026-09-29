-- Prove2me | Theorems.Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul
-- name    : ModularCurve.hasSum_qParam_heckeMatrix_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/9a719889-e00c-5d0a-a633-1a21b039407e
-- title:
--   Twisted q-expansion at period ℓ under τ↦(τ+b)/ℓ
-- statement:
--   Let $\ell$ be a natural number that is nonzero, $b$ a natural number, $A$ a formal Laurent series with complex coefficients (so $A$ has coefficients $A.\mathrm{coeff}\,m$ indexed by $m\in\mathbb Z$), and $F$ a complex-valued function on the upper half-plane. Assume that $F$ is expanded at period $1$ by $A$, in the sense that for every $\tau$ in the upper half-plane the family $m\mapsto A.\mathrm{coeff}\,m\cdot q_1(\tau)^m$, indexed by $m\in\mathbb Z$ with integer powers, is summable with sum $F(\tau)$; here $q_h(\tau)=\exp(2\pi i\tau/h)$ is Mathlib's `Function.Periodic.qParam`. Then for every $\tau$ in the upper half-plane the family $$m\mapsto\bigl(\exp(2\pi i\,b\,m/\ell)\cdot A.\mathrm{coeff}\,m\bigr)\cdot q_\ell(\tau)^m,\qquad m\in\mathbb Z,$$ is summable with sum $F(g\cdot\tau)$, where $g=\mathrm{ModularForm.heckeMatrix}\,\ell\,b$ is the invertible real matrix $\begin{pmatrix}1&b\\0&\ell\end{pmatrix}$ (the definition returns $1$ when $\ell=0$, a case excluded here) acting on the upper half-plane by Möbius transformations, so that $g\cdot\tau=(\tau+b)/\ell$. Thus $\tau\mapsto F((\tau+b)/\ell)$ is expanded at period $\ell$ by the series whose $m$-th coefficient is $\zeta_\ell^{bm}A.\mathrm{coeff}\,m$, $\zeta_\ell=e^{2\pi i/\ell}$.
--
--   This is the standard effect on $q$-expansions of the upper-triangular coset representatives $\begin{pmatrix}1&b\\0&\ell\end{pmatrix}$ used to define the Hecke operators $T_\ell$, $U_\ell$ and the modular polynomial $\Phi_\ell$: the coefficients are twisted by $\ell$-th roots of unity and the period changes from $1$ to $\ell$. It is used in the treatment of the $q$-expansions of the coset transforms entering $\Phi_\ell$ and of Fricke-type involutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_qParam_heckeMatrix_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeMatrix ℓ b • τ)) := by sorry
