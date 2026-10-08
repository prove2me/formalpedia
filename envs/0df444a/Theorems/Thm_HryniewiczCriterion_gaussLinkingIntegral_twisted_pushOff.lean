-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_twisted_pushOff
-- name    : HryniewiczCriterion.gaussLinkingIntegral_twisted_pushOff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T19:37:48.040627+00:00
-- url     : https://prove2.me/theorems/c9ca26e0-652e-4c48-ad4d-19424e9046b1
-- title:
--   Twisting formula: a push-off winding $k$ times around a knot in $S^3$ links it $k$ more times
-- statement:
--   Let $\gamma:\mathbb{R}\to S^3$ be a $C^2$, $1$-periodic loop, injective modulo $1$, and let $e_1,e_2$ be $C^2$, $1$-periodic vector fields along $\gamma$ with
--   $$\det\big(\gamma(s),\gamma'(s),e_1(s),e_2(s)\big)>0\qquad\text{for all } s,$$
--   so that $e_1,e_2$ span a positively oriented complement of $\gamma'$ in $T S^3$ (oriented as the boundary of the ball). Let $r>0$ and $\theta$ be $C^2$ with $r(s+1)=r(s)$ and $\theta(s+1)=\theta(s)+2\pi k$. For $\varepsilon>0$ put
--   $$B_0^\varepsilon(s)=\frac{\gamma+\varepsilon e_1}{|\gamma+\varepsilon e_1|},\qquad B_V^\varepsilon(s)=\frac{\gamma+\varepsilon r(\cos\theta\, e_1+\sin\theta\, e_2)}{|\cdot|}.$$
--   Then there are a pole $N\in S^3$ and $\varepsilon_0>0$ such that for $0<\varepsilon<\varepsilon_0$ the push-off $B_0^\varepsilon$ is well defined and disjoint from $\gamma$, $N$ misses $\gamma$, $B_0^\varepsilon$, $B_V^\varepsilon$, and the Gauss linking integrals from $N$ satisfy
--   $$\operatorname{Gauss}_N(\gamma,B_V^\varepsilon)=\operatorname{Gauss}_N(\gamma,B_0^\varepsilon)+k .$$
--
--   Proof idea: take $N$ off $\gamma$ and $\varepsilon$ so small that all push-offs stay in a thin tube around $\gamma$ away from $N$. The homotopy $r_\tau=(1-\tau)r+\tau$, $\theta_\tau=(1-\tau)\theta+\tau\cdot 2\pi k s$ stays in the tube minus $\gamma$, so by homotopy invariance of the Gauss integral we may take $r=1$, $\theta=2\pi k s$. Pulled back to the torus $(s,\varphi)\mapsto(\gamma+\varepsilon(\cos\varphi\,e_1+\sin\varphi\,e_2))/|\cdot|$, the Biot–Savart form of $\gamma$ is closed, so the curve of class $(1,k)$ has integral equal to that of the class $(1,0)$ plus $k$ times the meridian integral. The meridian integral is $1$ (Ampère's law), as the rescaling limit $\varepsilon\to 0$ shows: the knot becomes its tangent line and the meridian a circle around it, whose Gauss integral is $\tfrac{1}{2}\int_{\mathbb{R}}(1+v^2)^{-3/2}\,dv=1$. The sign is fixed by the orientation hypothesis.
-- source:
--   Twisting formula for framings of a knot (Rolfsen, Knots and Links, 1976, Ch. 5D; Geiges, An Introduction to Contact Topology, 2008, §3.5.2); needed for U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), Proposition 2.1.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.gaussLinkingIntegral_twisted_pushOff (γ e₁ e₂ : ℝ → R4)
    (hγ : ContDiff ℝ 2 γ) (he₁ : ContDiff ℝ 2 e₁) (he₂ : ContDiff ℝ 2 e₂)
    (hγper : ∀ s, γ (s + 1) = γ s) (he₁per : ∀ s, e₁ (s + 1) = e₁ s)
    (he₂per : ∀ s, e₂ (s + 1) = e₂ s) (hγunit : ∀ s, euclidNorm (γ s) = 1)
    (hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hdet : ∀ s, 0 < Matrix.det (Matrix.of ![γ s, deriv γ s, e₁ s, e₂ s]))
    (r θ : ℝ → ℝ) (hr : ContDiff ℝ 2 r) (hθ : ContDiff ℝ 2 θ) (hr0 : ∀ s, 0 < r s)
    (hrper : ∀ s, r (s + 1) = r s) (k : ℤ) (hθper : ∀ s, θ (s + 1) = θ s + 2 * Real.pi * k) :
    ∃ N : R4, euclidNorm N = 1 ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ s, γ s + ε • e₁ s ≠ 0) ∧
      (∀ s t, γ s ≠ radialNormalize (γ t + ε • e₁ t)) ∧
      (∀ s, γ s ≠ N ∧ radialNormalize (γ s + ε • e₁ s) ≠ N ∧
        radialNormalize (γ s + ε • (r s • (Real.cos (θ s) • e₁ s + Real.sin (θ s) • e₂ s))) ≠ N) ∧
      gaussLinkingIntegral N γ
          (fun s => radialNormalize (γ s + ε • (r s • (Real.cos (θ s) • e₁ s + Real.sin (θ s) • e₂ s)))) =
        gaussLinkingIntegral N γ (fun s => radialNormalize (γ s + ε • e₁ s)) + k := by sorry
