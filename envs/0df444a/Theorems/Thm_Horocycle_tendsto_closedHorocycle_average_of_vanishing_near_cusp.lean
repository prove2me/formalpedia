-- Prove2me | Theorems.Thm_Horocycle_tendsto_closedHorocycle_average_of_vanishing_near_cusp
-- name    : Horocycle.tendsto_closedHorocycle_average_of_vanishing_near_cusp
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T20:12:43.755627+00:00
-- url     : https://prove2.me/theorems/0600118f-8078-4d47-a9cc-5ed4e9d8f109
-- title:
--   Equidistribution of long closed horocycles on $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$ for compactly supported test functions: $\int_0^1 f(x+iy)\,dx\to\frac3\pi\int_{\mathcal D}f\,d\mu$
-- statement:
--   **Equidistribution of long closed horocycles on the modular surface, for compactly supported test functions.** Let $\mathbb H=\{z\in\mathbb C:\operatorname{Im}z>0\}$ carry the hyperbolic measure $d\mu(z)=\dfrac{dx\,dy}{y^2}$ ($z=x+iy$), let $\mathrm{SL}_2(\mathbb Z)$ act on $\mathbb H$ by Möbius transformations, and let
--   $$\mathcal D=\{z\in\mathbb H:\ |z|\ge1,\ |\operatorname{Re}z|\le\tfrac12\}$$
--   be the standard fundamental domain, of hyperbolic area $\mu(\mathcal D)=\pi/3$. Let $f:\mathbb H\to\mathbb C$ be a continuous function such that
--
--   1. $f(\gamma z)=f(z)$ for all $\gamma\in\mathrm{SL}_2(\mathbb Z)$ and $z\in\mathbb H$;
--   2. $f$ vanishes near the cusp: there is $T\in\mathbb R$ with $f(z)=0$ for every $z\in\mathbb H$ with $\operatorname{Im}z\ge T$.
--
--   Then
--   $$\lim_{y\to0^+}\int_0^1 f(x+iy)\,dx=\frac{3}{\pi}\int_{\mathcal D}f(z)\,\frac{dx\,dy}{y^2}.$$
--
--   The functions satisfying 1 and 2 are exactly the pull-backs to $\mathbb H$ of the continuous functions with compact support on the modular surface $M=\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$. For $y>0$ the image in $M$ of the segment $\{x+iy:0\le x\le1\}$ is the closed horocycle at height $y$, of hyperbolic length $1/y$, and $dx$ on $[0,1]$ is its normalized arc length. So the theorem says that the normalized arc-length measures of the long closed horocycles converge vaguely to the normalized hyperbolic measure $\frac3\pi\mu$ as $y\to0^+$. This is the leading term of Sarnak's expansion (7.1.2.4), recalled in §7.1.2 (pp. 318–320) of the paper, for $\Gamma=\mathrm{SL}_2(\mathbb Z)$ and test functions on $M$; for this group it goes back to Zagier, whom the paper also cites there. Since all the measures involved are probability measures, it implies the equidistribution of long closed horocycles against all bounded continuous invariant test functions (Horocycle.tendsto_closedHorocycle_average_modularGroup).
--
--   **Formalization Note.** Mathlib's `volume` on `ℍ` is the measure $dx\,dy/y^2$, `ModularGroup.fd` is $\mathcal D$, and the horocycle point is `UpperHalfPlane.ofComplex (x + y * I)`, which is $x+iy$ for $y>0$ (the junk value for $y\le0$ is irrelevant along the filter $y\to0^+$). Condition 2 is the hypothesis `∃ T, ∀ z, T ≤ z.im → f z = 0`; since every point of $\mathbb H$ is $\mathrm{SL}_2(\mathbb Z)$-equivalent to a point of $\mathcal D$, an invariant $f$ satisfying it is determined by its values on the compact set $\{z\in\mathcal D:\operatorname{Im}z\le T\}$, so no boundedness hypothesis is needed. **Deviation from the source.** Sarnak's Theorem 1 is stated on $T^1M$, for general $\Gamma$, with smooth compactly supported test functions and an asymptotic expansion; here only the limit is stated, for $\Gamma=\mathrm{SL}_2(\mathbb Z)$, with continuous compactly supported test functions on $M$ (pulled back to $T^1M$); a continuous function with compact support on $M$ is a uniform limit of smooth ones supported in a fixed compact set, so the limit for smooth test functions gives the limit for continuous ones.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 16, §1.2.5 (Recollections from Sarnak's equidistribution of long horocycles), and §7.1.2, (7.1.2.4), pp. 318–320; auxiliary lemma for the proof of Horocycle.tendsto_closedHorocycle_average_modularGroup; classical reference: P. Sarnak, Asymptotic Behavior of Periodic Orbits of the Horocycle Flow and Eisenstein Series, Comm. Pure Appl. Math. 34 (1981), 719–739, §0, Thm. 1 (as cited on p. 319); see also D. Zagier, Eisenstein Series and the Riemann Zeta Function, in: Automorphic Forms, Representation Theory and Arithmetic, Springer, 1981, §1 (cited on p. 319)

import Mathlib

open UpperHalfPlane MeasureTheory Filter Topology
open scoped MatrixGroups

set_option autoImplicit false

namespace Horocycle

/-- Equidistribution of long closed horocycles on `SL(2,ℤ)\ℍ` for compactly supported test
functions: if `f` is continuous, `SL(2,ℤ)`-invariant and vanishes on the cusp neighbourhood
`{z : T ≤ im z}` for some `T` (i.e. `f` is a compactly supported continuous function on the modular
surface), then the average of `f` over the closed horocycle `{x + i y : 0 ≤ x ≤ 1}` tends, as
`y → 0⁺`, to `(3/π) ∫_𝒟 f dμ`, where `μ = dx dy / y²` is `volume` on `ℍ` and
`𝒟 = ModularGroup.fd`. -/
theorem tendsto_closedHorocycle_average_of_vanishing_near_cusp (f : ℍ → ℂ) (hf : Continuous f)
    (hΓ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z)
    (hcusp : ∃ T : ℝ, ∀ z : ℍ, T ≤ z.im → f z = 0) :
    Tendsto
      (fun y : ℝ => ∫ x in (0 : ℝ)..1,
        f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 ((3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, f z)) := by sorry

end Horocycle
