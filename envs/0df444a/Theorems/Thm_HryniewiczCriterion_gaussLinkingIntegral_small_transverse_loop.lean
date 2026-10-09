-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_small_transverse_loop
-- name    : HryniewiczCriterion.gaussLinkingIntegral_small_transverse_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T19:10:34.873946+00:00
-- url     : https://prove2.me/theorems/9a27c5dc-5565-4184-9d5c-dc930af3cce1
-- title:
--   A small loop on a surface crossing a knot transversally has Gauss linking integral $\pm1$ with the knot
-- statement:
--   Let $E:\mathbb{R}^2\to\mathbb{R}^4$ be $C^2$ on a ball $B(z,r)$ with $|E|=1$ there, so $E$ is a small surface in $S^3$. Let $\gamma:\mathbb{R}\to S^3$ be a $C^2$ knot (period $1$, injective modulo $1$) which meets $E(B(z,r))$ only at $E(z)=\gamma(t_0)$, transversally:
--   $$d:=\det\big(\gamma(t_0),\gamma'(t_0),\partial_1E(z),\partial_2E(z)\big)\neq0$$
--   (rows of a $4\times4$ matrix). Let $N\in S^3$ miss $\gamma$ and $E(B(z,r))$. Then for all sufficiently small $\rho>0$ the loop $s\mapsto E(z+\rho(\cos2\pi s,\sin2\pi s))$ has Gauss linking integral (`gaussLinkingIntegral`, stereographic projection from $N$) with $\gamma$ equal to $\operatorname{sign}(d)=\pm1$.
--
--   Suggested proof. Shift the parameter of $\gamma$ so $t_0=0$. Taylor expansion gives $E(z+\rho w)=\gamma(0)+\rho\,dE(z)w+O(\rho^2)$, while a tube estimate (the knot is embedded and $dE(z)w$ is transverse to $\gamma'(0)$ inside $T_{\gamma(0)}S^3$) keeps both $E(z+\rho w)$ and $\nu(\gamma(0)+\rho\,dE(z)w)$, $|w|=1$, at distance $\ge c\rho$ from $\gamma$, so the straight-line homotopy between them (normalized to $S^3$) misses $\gamma$ for small $\rho$. By homotopy invariance the Gauss integral equals that of the round meridian $\nu(\gamma(0)+\rho(\cos 2\pi s\,f_1+\sin2\pi s\,f_2))$, $f_i=\partial_iE(z)$, which is $1$ when $d>0$ (`gaussLinkingIntegral_meridian_eq_one`, using the symmetry of the Gauss integrand in the two loops). If $d<0$, reverse the meridian ($s\mapsto -s$), which changes the sign.
-- source:
--   D. Rolfsen, Knots and Links, Publish or Perish 1976, Ch. 5D (linking number = algebraic intersection number with a Seifert surface); the case of a straight meridian is the published `gaussLinkingIntegral_meridian_eq_one`.

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_small_transverse_loop (E : Plane → R4) (z : Plane) (r : ℝ) (hr : 0 < r)
    (hE : ContDiffOn ℝ 2 E (Metric.ball z r))
    (hEunit : ∀ v ∈ Metric.ball z r, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (t₀ : ℝ) (hz : E z = γ t₀)
    (hmiss : ∀ v ∈ Metric.ball z r, v ≠ z → ∀ t, E v ≠ γ t)
    (hdet : Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
        fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) ≠ 0)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ Metric.ball z r, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ =
        if 0 < Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
          fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) then 1 else -1 := by sorry
