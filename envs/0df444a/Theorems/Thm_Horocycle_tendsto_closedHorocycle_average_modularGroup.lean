-- Prove2me | Theorems.Thm_Horocycle_tendsto_closedHorocycle_average_modularGroup
-- name    : Horocycle.tendsto_closedHorocycle_average_modularGroup
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T18:34:59.91801+00:00
-- url     : https://prove2.me/theorems/51a40163-00b8-4561-aecd-c6131a3254a0
-- title:
--   Equidistribution of long closed horocycles on $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$: $\int_0^1 f(x+iy)\,dx\to\frac3\pi\int_{\mathcal D}f\,\frac{dx\,dy}{y^2}$ as $y\to0^+$
-- statement:
--   **Equidistribution of long closed horocycles on the modular surface.** Let $\mathbb H=\{z\in\mathbb C:\operatorname{Im}z>0\}$ carry the $\mathrm{SL}_2(\mathbb R)$-invariant hyperbolic measure $d\mu(z)=\dfrac{dx\,dy}{y^2}$ ($z=x+iy$), let $\mathrm{SL}_2(\mathbb Z)$ act on $\mathbb H$ by Möbius transformations, and let
--   $$\mathcal D=\{z\in\mathbb H:\ |z|\ge1,\ |\operatorname{Re}z|\le\tfrac12\}$$
--   be the standard fundamental domain, of hyperbolic area $\mu(\mathcal D)=\pi/3$. For $y>0$ the image in $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$ of the segment $\{x+iy:0\le x\le1\}$ is the closed horocycle at height $y$, a closed orbit of the horocycle flow of hyperbolic length $1/y$, and $dx$ on $[0,1]$ is its normalized arc length. Then for every bounded continuous function $f:\mathbb H\to\mathbb C$ with $f(\gamma z)=f(z)$ for all $\gamma\in\mathrm{SL}_2(\mathbb Z)$ and $z\in\mathbb H$,
--   $$\lim_{y\to0^+}\int_0^1 f(x+iy)\,dx=\frac{3}{\pi}\int_{\mathcal D}f(z)\,\frac{dx\,dy}{y^2}.$$
--   In words: as their length $1/y$ tends to $+\infty$, the closed horocycles of $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$ become equidistributed with respect to the normalized hyperbolic measure $\frac3\pi\,\mu$.
--
--   **Role in the source.** §1.2.5 (p. 16) of the paper is titled "Recollections from Sarnak's equidistribution of long horocycles", and p. 21 compares the "equivariant supports" of its dual basis elements with Sarnak's paper on long horocycles (footnote 3). The theorem is recalled in §7.1.2 (pp. 318–320): for a non-compact finite-area $M=\Gamma\backslash\mathbb H$, the probability measures $\nu^{(k)}(t)$ on the closed horocycle orbits of period $t^{-1}$ in $T^1M$ satisfy $\nu^{(k)}(t)=\frac{\mu}{2\pi V}+\sum_{1\le m\le N}t^{1-s_m}\mu^{(k)}_m+o(t^{1/2})$ as $t\to0^+$ (7.1.2.4), whose "geometric meaning" is that long horocycles distribute themselves uniformly. The statement above is the leading term of this expansion for $\Gamma=\mathrm{SL}_2(\mathbb Z)$, tested on functions on $M$; for this group it goes back to Zagier, whom the paper also cites there.
--
--   **Formalization Note.** Mathlib's `volume` on `ℍ` is the measure $dx\,dy/y^2$, `ModularGroup.fd` is $\mathcal D$, and the horocycle point is `UpperHalfPlane.ofComplex (x + y * I)`, which is $x+iy$ for $y>0$ (the junk value for $y\le0$ is irrelevant along the filter $y\to0^+$). Continuous bounded $\mathrm{SL}_2(\mathbb Z)$-invariant functions on $\mathbb H$ are exactly the bounded continuous functions on the quotient, and $\partial\mathcal D$ is $\mu$-null, so $\int_{\mathcal D}$ is the integral over $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$. **Deviation from the source.** Sarnak's Theorem 1 is stated on $T^1M$, for general $\Gamma$, with smooth compactly supported test functions and an asymptotic expansion; here only the limit is stated, for $\Gamma=\mathrm{SL}_2(\mathbb Z)$ and functions on $M$ (pulled back to $T^1M$); the class of bounded continuous test functions is the usual meaning of equidistribution (all measures involved are probability measures, so convergence on $C_c$ implies convergence on bounded continuous functions). For $f\equiv1$ both sides equal $1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 16, §1.2.5 (Recollections from Sarnak's equidistribution of long horocycles), p. 21 (footnote 3), and §7.1.2, (7.1.2.4), pp. 318–320; classical reference: P. Sarnak, Asymptotic Behavior of Periodic Orbits of the Horocycle Flow and Eisenstein Series, Comm. Pure Appl. Math. 34 (1981), 719–739, §0, Thm. 1 (as cited on p. 319); see also D. Zagier, Eisenstein Series and the Riemann Zeta Function, in: Automorphic Forms, Representation Theory and Arithmetic, Springer, 1981, §1 (cited on p. 319)

import Mathlib

open UpperHalfPlane MeasureTheory Filter Topology
open scoped MatrixGroups

set_option autoImplicit false

namespace Horocycle

/-- Equidistribution of long closed horocycles on `SL(2,ℤ)\ℍ`: for a bounded continuous
`SL(2,ℤ)`-invariant `f`, the average of `f` over the closed horocycle `{x + i y : 0 ≤ x ≤ 1}`
tends, as `y → 0⁺`, to `(3/π) ∫_𝒟 f dμ`, where `μ = dx dy / y²` is the hyperbolic measure
(`volume` on `ℍ`) and `𝒟 = ModularGroup.fd` is the standard fundamental domain (`μ 𝒟 = π/3`). -/
theorem tendsto_closedHorocycle_average_modularGroup (f : ℍ → ℂ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ z : ℍ, ‖f z‖ ≤ C)
    (hΓ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z) :
    Tendsto
      (fun y : ℝ => ∫ x in (0 : ℝ)..1,
        f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 ((3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, f z)) := by sorry

end Horocycle
