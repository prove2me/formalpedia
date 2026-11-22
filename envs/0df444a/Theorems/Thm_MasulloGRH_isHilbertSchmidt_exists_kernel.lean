-- Prove2me | Theorems.Thm_MasulloGRH_isHilbertSchmidt_exists_kernel
-- name    : MasulloGRH.isHilbertSchmidt_exists_kernel
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:34.324484+00:00
-- url     : https://prove2.me/theorems/d9f1694c-3d56-451b-b976-10de36ed64a0
-- title:
--   Every Hilbert–Schmidt operator on $L^2(X,\mu)$ is an integral operator with a unique kernel $k\in L^2(X\times X,\mu\otimes\mu)$, and $\|T\|_{S_2}=\|k\|_{L^2}$
-- statement:
--   **Hilbert–Schmidt operators on $L^2$ are the integral operators with square-integrable kernels.**
--
--   Let $X$ be a second countable locally compact Hausdorff space and $\mu$ a Radon measure on $X$. A bounded operator $T$ on the Hilbert space $L^2(X,\mu)$ is **Hilbert–Schmidt** if $\sum_{\phi\in\Sigma}\|T\phi\|^2<\infty$ for an orthonormal basis $\Sigma$, and its Hilbert–Schmidt norm is $\|T\|_{S_2}=\big(\sum_{\phi\in\Sigma}\|T\phi\|^2\big)^{1/2}$.
--
--   Let $T$ be a Hilbert–Schmidt operator on $L^2(X,\mu)$. Then there is a kernel $k\in L^2(X\times X,\mu\otimes\mu)$ such that for every $\phi\in L^2(X,\mu)$
--   $$(T\phi)(x)=\int_Xk(x,y)\,\phi(y)\,d\mu(y)\qquad\text{for $\mu$-almost every }x\in X$$
--   (the integral being absolutely convergent for almost every $x$), and
--   $$\|T\|_{S_2}=\|k\|_{L^2(X\times X,\mu\otimes\mu)} .$$
--   The kernel is unique: any $k'\in L^2(X\times X,\mu\otimes\mu)$ representing $T$ in the same way is equal to $k$ $\mu\otimes\mu$-almost everywhere.
--
--   Together with the converse (an $L^2$ kernel defines a Hilbert–Schmidt operator with $\|T\|_{S_2}=\|k\|_{L^2}$, part (1) of Theorem C.3.7.1, already on the platform as `MasulloGRH.trace_formula_integral_operators`) this is the identification $S_2(L^2(X,\mu))=L^2(X\times X,\mu\otimes\mu)$ of (C.3.6.5). In particular every nuclear operator on $L^2(X,\mu)$, being Hilbert–Schmidt, has such a kernel; this is the starting point of the trace formula $\operatorname{Trace}(T)=\int_Xk(x,x)\,d\mu(x)$ for integral operators in §C.3.7.
--
--   **Formalization Note.** `IsHilbertSchmidt` and `hilbertSchmidtNorm` are from `Def_MasulloGRH_HilbertNuclear` (sums over one fixed orthonormal basis of $L^2(X,\mu)$ = `Lp ℂ 2 μ`). The measure is a regular, $\sigma$-finite Borel measure, as in the platform statement of Theorem C.3.7.1; the kernel is a function on $X\times X$ with `MemLp k 2 (μ.prod μ)`, and the kernel is applied in the convention $(T\phi)(x)=\int k(x,y)\phi(y)\,d\mu(y)$ of (C.3.7.1). The paper states (C.3.6.5) for operators $L^2(X,\mu)\to L^2(Y,\nu)$ between two such spaces; the platform notion of Hilbert–Schmidt operator is for endomorphisms, so the statement is the case $Y=X$, $\nu=\mu$ (the form used in §C.3.7).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 705, §C.3.6.1, (C.3.6.5)–(C.3.6.6), and p. 707, §C.3.7 (second paragraph)

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear

open Filter Topology MeasureTheory
set_option autoImplicit false

namespace MasulloGRH

theorem isHilbertSchmidt_exists_kernel
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : IsHilbertSchmidt T) :
    ∃ k : X × X → ℂ, MemLp k 2 (μ.prod μ) ∧
      (∀ ϕ : Lp ℂ 2 μ, ∀ᵐ x ∂μ,
        Integrable (fun y => k (x, y) * ϕ y) μ ∧ T ϕ x = ∫ y, k (x, y) * ϕ y ∂μ) ∧
      hilbertSchmidtNorm T = (eLpNorm k 2 (μ.prod μ)).toReal ∧
      ∀ k' : X × X → ℂ, MemLp k' 2 (μ.prod μ) →
        (∀ ϕ : Lp ℂ 2 μ, ∀ᵐ x ∂μ, T ϕ x = ∫ y, k' (x, y) * ϕ y ∂μ) →
        k' =ᵐ[μ.prod μ] k := by sorry

end MasulloGRH
