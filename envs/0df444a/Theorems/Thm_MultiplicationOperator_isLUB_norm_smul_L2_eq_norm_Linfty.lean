-- Prove2me | Theorems.Thm_MultiplicationOperator_isLUB_norm_smul_L2_eq_norm_Linfty
-- name    : MultiplicationOperator.isLUB_norm_smul_L2_eq_norm_Linfty
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:42:57.505615+00:00
-- url     : https://prove2.me/theorems/aa0dc64a-5bcd-42cd-9cfb-17b75e52406a
-- title:
--   Norm of a multiplication operator: $\|M_\varphi\|_{L^2\to L^2}=\|\varphi\|_{\infty}$ for $\varphi\in L^\infty(\mu)$ and $\mu$ $\sigma$-finite
-- statement:
--   **The norm of a multiplication operator.** Let $(X,\mathcal A,\mu)$ be a $\sigma$-finite measure space and let $\varphi\in L^\infty(X,\mu)$ be a complex-valued essentially bounded function. The multiplication operator
--   $$M_\varphi\colon L^2(X,\mu)\to L^2(X,\mu),\qquad M_\varphi g=\varphi g,$$
--   is bounded with operator norm equal to the essential supremum of $|\varphi|$:
--   $$\|M_\varphi\|=\sup\big\{\|\varphi g\|_{2}\ :\ g\in L^2(X,\mu),\ \|g\|_2\le 1\big\}=\|\varphi\|_\infty .$$
--
--   The inequality $\|\varphi g\|_2\le\|\varphi\|_\infty\|g\|_2$ is Hölder's inequality. The content of the theorem is that the bound is sharp. In particular $\varphi\mapsto M_\varphi$ is an isometric embedding of $L^\infty(\mu)$ into the bounded operators on $L^2(\mu)$, so $\rho_m\to\rho$ in $L^\infty$ implies $M_{\rho_m}\to M_\rho$ in operator norm. This is how the paper uses the result (p. 501, proof of Theorem 12.1.1.2(2)): it approximates an $L^\infty$ cutoff by simple functions and passes to the limit in trace norm. The hypothesis of $\sigma$-finiteness cannot be dropped. If $\mu$ is the measure on a one-point space that gives the point mass $\infty$, then $L^2(\mu)=\{0\}$, while $\varphi=1$ has $\|\varphi\|_\infty=1$.
--
--   **Formalization Note.** $\varphi\in$ `Lp ℂ ∞ μ` and $g\in$ `Lp ℂ 2 μ`. The product `φ • g` is Mathlib's Hölder product $L^\infty\times L^2\to L^2$, which is almost everywhere equal to the pointwise product `⇑φ • ⇑g` (`MeasureTheory.Lp.coeFn_lpSMul`). The norm identity is stated as: $\|\varphi\|_\infty$ is the least upper bound of the set of numbers $\|\varphi g\|_2$ with $\|g\|_2\le1$. This set is exactly the set of values of $M_\varphi$ on the closed unit ball, so its least upper bound is the operator norm. The upper-bound half is already in Mathlib (`MeasureTheory.Lp.norm_smul_le`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 501, proof of Theorem 12.1.1.2(2); classical reference: J. B. Conway, A Course in Functional Analysis, Springer (the paper's [Cnw-a]), Ch. II, §1, Thm. 1.5, p. 28, cited by the paper at this step

import Mathlib

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace MultiplicationOperator

/-- The multiplication operator `M_φ g = φ • g` by `φ ∈ L^∞(μ)` on `L^2(μ)`, `μ` σ-finite, has
operator norm `‖φ‖_∞`: the norm `‖φ‖_∞` is the least upper bound of `‖φ • g‖₂` over the closed
unit ball of `L^2(μ)`. -/
theorem isLUB_norm_smul_L2_eq_norm_Linfty
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (φ : Lp ℂ ∞ μ) :
    IsLUB {r : ℝ | ∃ g : Lp ℂ 2 μ, ‖g‖ ≤ 1 ∧ r = ‖φ • g‖} ‖φ‖ := by sorry

end MultiplicationOperator
