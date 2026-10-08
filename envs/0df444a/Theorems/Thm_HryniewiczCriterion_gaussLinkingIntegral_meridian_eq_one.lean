-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_meridian_eq_one
-- name    : HryniewiczCriterion.gaussLinkingIntegral_meridian_eq_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:18:10.632978+00:00
-- url     : https://prove2.me/theorems/5adb7ce6-c78b-4e28-ac45-61692d8c3389
-- title:
--   A small meridian circle of a knot in $S^3$ has Gauss linking integral $1$ with the knot
-- statement:
--   Let $\gamma:\mathbb{R}\to S^3\subset\mathbb{R}^4$ be a $C^2$ loop with $\gamma(s+1)=\gamma(s)$, injective modulo $1$ (that is, $\gamma(s)=\gamma(t)$ implies $t-s\in\mathbb{Z}$). Let $f_1,f_2\in\mathbb{R}^4$ satisfy
--   $$\det\big(\gamma(0),\gamma'(0),f_1,f_2\big)>0,$$
--   and let $N\in S^3$ be a pole not on $\gamma$. For $\varepsilon>0$ consider the meridian loop
--   $$m_\varepsilon(t)=\frac{\gamma(0)+\varepsilon\big(\cos(2\pi t)f_1+\sin(2\pi t)f_2\big)}{\big|\gamma(0)+\varepsilon\big(\cos(2\pi t)f_1+\sin(2\pi t)f_2\big)\big|},$$
--   a small circle around $\gamma(0)$ that turns from $f_1$ towards $f_2$. Then for all sufficiently small $\varepsilon>0$ the Gauss linking integral of $\gamma$ and $m_\varepsilon$, computed after stereographic projection from $N$ (`gaussLinkingIntegral`), equals $1$.
--
--   Proof idea: the integral does not depend on $\varepsilon$ (fixed-pole homotopy invariance, `gaussIntegral_eq_of_homotopy`), nor on the frame within the positively oriented ones. After stereographic projection, deform $\gamma$ near $s=0$ to an exact straight segment through the centre of a round meridian circle of radius $\rho$ in the normal plane. The straight piece contributes exactly $\frac{1}{4\pi}\cdot 2\pi\rho^2\int_{-\delta}^{\delta}\frac{dx}{(x^2+\rho^2)^{3/2}}\to 1$ as $\rho\to0$. The rest contributes $O(\rho)$, since the circle has length $2\pi\rho$ and stays a fixed distance from the rest of the curve. Numerically checked with the exact Lean integrand: $1.0000000$ at $\varepsilon=0.1$ and $0.03$ on a non-planar loop with a skewed frame.
-- source:
--   D. Rolfsen, Knots and Links, Publish or Perish, 1976, Ch. 5D (linking number via the Gauss integral; a meridian links its knot once; framings and the twisting of push-offs); used for self-linking numbers in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 1.5.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.gaussLinkingIntegral_meridian_eq_one (γ : ℝ → R4)
    (hγ : ContDiff ℝ 2 γ) (hγper : ∀ s, γ (s + 1) = γ s) (hγunit : ∀ s, euclidNorm (γ s) = 1)
    (hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n) (f₁ f₂ : R4)
    (hdet : 0 < Matrix.det (Matrix.of ![γ 0, deriv γ 0, f₁, f₂]))
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ s ≠ N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      gaussLinkingIntegral N γ (fun t => radialNormalize (γ 0 +
        ε • (Real.cos (2 * Real.pi * t) • f₁ + Real.sin (2 * Real.pi * t) • f₂))) = 1 := by sorry
