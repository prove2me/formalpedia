-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_strip_bump_jump
-- name    : HryniewiczCriterion.gaussLinkingIntegral_strip_bump_jump
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:55:06.090779+00:00
-- url     : https://prove2.me/theorems/1286c73c-3f55-4100-8ed4-1159186480fc
-- title:
--   Raising a graph loop over one puncture adds a small loop around it to the Gauss linking integral
-- statement:
--   Setting. $E:\mathbb R^2\to\mathbb R^4$ is $C^2$ near the closed unit disk $\overline{\mathbb D}$ with $|E|=1$ on $\overline{\mathbb D}$; $\gamma:\mathbb R\to S^3$ is a $C^2$ loop of period $1$ meeting $E(\overline{\mathbb D})$ only over a finite set $Z$; $N\in S^3$ misses $\gamma$ and $E(\overline{\mathbb D})$. For a centre $c\in\mathbb D$ use strip coordinates $\Psi(\mu,s)=c+\mu(\partial(s)-c)$, $\partial(s)=(\cos2\pi s,\sin2\pi s)$, and for a $1$-periodic $h$ with values in $[0,1]$ the graph loop $\ell_h(s)=\Psi(h(s),s)$.
--
--   Statement. Let $z=\Psi(a_0,s_0)$ and $0<\delta<1/4$. Let $g,b$ be $C^2$ and $1$-periodic with $g\ge0$, $b\ge0$, $g+b\le1$, $b=0$ outside $s_0+(-\delta,\delta)+\mathbb Z$, and $g(s_0)<a_0<g(s_0)+b(s_0)$. Assume the only point of $Z$ in $\Psi([0,1]\times[s_0-2\delta,s_0+2\delta])$ is (possibly) $z$, and that $\ell_g,\ell_{g+b}$ miss $Z$. Then for all small $\rho>0$
--   $$\mathrm{Gauss}_N(E\circ\ell_{g+b},\gamma)=\mathrm{Gauss}_N(E\circ\ell_g,\gamma)+\mathrm{Gauss}_N\big(E\circ(z+\rho\,\partial),\gamma\big).$$
--
--   Suggested proof (homotopies and a substitution only).
--   1. *Lens loop.* With $s(\sigma)=s_0-\delta'\cos2\pi\sigma$ ($\delta<\delta'<2\delta$, so $b=0$ near $s_0\pm\delta'$) let $\Lambda(\sigma)=(g(s(\sigma))+\chi(\sigma)\,b(s(\sigma)),\,s(\sigma))$ where $\chi$ is the indicator of $[0,\tfrac12]+\mathbb Z$; $\Lambda$ is $C^2$ and $1$-periodic. The outer Gauss integrand depends only on the point and the velocity of the loop and is linear in the velocity, so substituting $s=s(\sigma)$ on each half gives $\mathrm{Gauss}(E\circ\Psi\circ\Lambda)=\int_{s_0-\delta'}^{s_0+\delta'}(f_{g+b}-f_g)\,ds=\mathrm{Gauss}(E\circ\ell_{g+b})-\mathrm{Gauss}(E\circ\ell_g)$, because $\ell_{g+b}=\ell_g$ off the interval.
--   2. *Lens to ellipse.* The straight-line homotopy (in the first coordinate only) from $\Lambda$ to the ellipse $(m+\eta\sin2\pi\sigma,\,s(\sigma))$, $m\pm\eta=$ the values $g(s_0)+b(s_0)$ and $g(s_0)$, stays in $[0,1]\times[s_0-\delta',s_0+\delta']$ and keeps the first coordinate $>a_0$ at $\sigma=\tfrac14$ and $<a_0$ at $\sigma=\tfrac34$, the only times with $s=s_0$; so it misses $z$ and, by hypothesis, all of $Z$. Shrink the ellipse to one centred at $(a_0,s_0)$ in the same way.
--   3. *Ellipse to round circle.* $\det D\Psi(a_0,s_0)=2\pi a_0(1-\langle c,\partial(s_0)\rangle)>0$; for a small ellipse $\Psi((a_0,s_0)+r w(\sigma))$ is homotopic to $z+r\,D\Psi\, w(\sigma)$ (Taylor, the error is $O(r^2)$ against a lower bound $\ge cr$), then within $\mathrm{GL}^+(2)$ (write the linear loop as $\alpha e^{2\pi i\sigma}+\beta e^{-2\pi i\sigma}$ with $|\alpha|>|\beta|$, kill $\beta$, rotate $\alpha$ to $|\alpha|$) to $z+\rho\,\partial$, all inside a small punctured disk around $z$. Homotopy invariance of the Gauss integral (`gaussLinkingIntegral_planar_homotopy`) finishes the proof.
-- source:
--   Residue formula for the Gauss linking integral (homological invariance), e.g. D. Rolfsen, Knots and Links, Publish or Perish 1976, Ch. 5D

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_strip_bump_jump (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (Z : Finset Plane) (hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ closedUnitDisk, E v ≠ N)
    (c : Plane) (hc : c ∈ openUnitDisk) (z : Plane) (a₀ s₀ δ : ℝ)
    (hz : z = c + a₀ • (circlePoint s₀ - c)) (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (g b : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hb : ContDiff ℝ 2 b)
    (hgper : ∀ s, g (s + 1) = g s) (hbper : ∀ s, b (s + 1) = b s)
    (hgb : ∀ s, 0 ≤ g s ∧ 0 ≤ b s ∧ g s + b s ≤ 1)
    (hbsupp : ∀ s, b s ≠ 0 → ∃ n : ℤ, |s - s₀ - n| < δ)
    (hlow : g s₀ < a₀) (hhigh : a₀ < g s₀ + b s₀)
    (hstrip : ∀ s μ : ℝ, |s - s₀| ≤ 2 * δ → 0 ≤ μ → μ ≤ 1 →
      c + μ • (circlePoint s - c) ∈ Z → c + μ • (circlePoint s - c) = z)
    (hgZ : ∀ s, c + g s • (circlePoint s - c) ∉ Z)
    (hgbZ : ∀ s, c + (g s + b s) • (circlePoint s - c) ∉ Z) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (c + (g s + b s) • (circlePoint s - c))) γ =
        gaussLinkingIntegral N (fun s => E (c + g s • (circlePoint s - c))) γ +
          gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ := by sorry
