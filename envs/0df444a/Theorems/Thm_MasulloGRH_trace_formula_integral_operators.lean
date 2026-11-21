-- Prove2me | Theorems.Thm_MasulloGRH_trace_formula_integral_operators
-- name    : MasulloGRH.trace_formula_integral_operators
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:06:38.972786+00:00
-- url     : https://prove2.me/theorems/e0fc0030-2d95-4de0-ac98-dfbb4ee64cb8
-- title:
--   Theorem C.3.7.1 (1), (2a) — trace formula for integral operators: $\operatorname{Trace}(T)=\int_Xk(x,x)\,d\mu(x)$
-- statement:
--   An operator $T$ on a Hilbert space $H$ is **nuclear** (trace class) if $Tu=\sum_m\langle u,x_m\rangle y_m$ with $\sum_m\|x_m\|\|y_m\|<\infty$. Its **trace** is $\operatorname{Trace}(T)=\sum_\varphi\langle T\varphi,\varphi\rangle$ over an orthonormal basis, and its **trace norm** is $\|T\|_{\mathrm{Tr}}=\operatorname{Trace}|T|$ with $|T|=(T^*T)^{1/2}$.
--
--   Let $X$ be a second countable locally compact Hausdorff space with a Radon measure $\mu$, and let $k\in L^2(X\times X,\mu\otimes\mu)$. Then:
--
--   1. The integral operator
--   $$(T\varphi)(x)=\int_Xk(x,y)\,\varphi(y)\,d\mu(y)$$
--   is a bounded operator on $L^2(X,\mu)$, it is Hilbert–Schmidt, and $\|T\|_{S_2}=\|k\|_{L^2(X\times X,\mu\otimes\mu)}$.
--   2. If $T$ is nuclear and for $\mu$-almost every $x$ the kernel $k$ is continuous at the diagonal point $(x,x)$, then $x\mapsto k(x,x)$ is integrable and
--   $$\operatorname{Trace}(T)=\int_Xk(x,x)\,d\mu(x).$$
--
--   This is the formula by which the trace of an integral operator is read off from its kernel on the diagonal. The geometric side of the draft's trace formula is a computation of this kind on the idele class group.
--
--   **Formalization Note** A Radon measure is a regular Borel measure, taken $\sigma$-finite. "Continuous almost everywhere along the diagonal" is stated as: for $\mu$-almost every $x$, $k$ is continuous at $(x,x)$. Part (2b) of the source, on a smoothening of the kernel along the diagonal, is not included.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.3.7, Theorem C.3.7.1 (Trace formula for integral nuclear operators), parts (1) and (2a), eqs. (C.3.7.1)–(C.3.7.2), p. 708

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory Filter Topology

theorem trace_formula_integral_operators
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] [SigmaFinite μ] (k : X → X → ℂ)
    (hk : MemLp (fun p : X × X => k p.1 p.2) 2 (μ.prod μ)) :
    ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      (∀ ϕ : Lp ℂ 2 μ, ∀ᵐ x ∂μ, T ϕ x = ∫ y, k x y * ϕ y ∂μ) ∧
      IsHilbertSchmidt T ∧
      hilbertSchmidtNorm T = (eLpNorm (fun p : X × X => k p.1 p.2) 2 (μ.prod μ)).toReal ∧
      (IsNuclearOperator T →
        (∀ᵐ x ∂μ, ContinuousAt (fun p : X × X => k p.1 p.2) (x, x)) →
        Integrable (fun x => k x x) μ ∧ operatorTrace T = ∫ x, k x x ∂μ) := by sorry

end MasulloGRH
