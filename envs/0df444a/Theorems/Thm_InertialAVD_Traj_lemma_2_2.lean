-- Prove2me | Theorems.Thm_InertialAVD_Traj_lemma_2_2
-- name    : InertialAVD.Traj.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:05.245799+00:00
-- url     : https://prove2.me/theorems/b5243267-a62a-4eba-9b73-1cc4774b2e78
-- title:
--   Lemma 2.2 — $\int_{t_0}^t\frac1s(W(s)-\Phi(z))\,ds\le C-\frac1t\dot h_z(t)-\frac{3}{2\alpha}W(t)$ with the explicit constant $C$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable, $\alpha>0$, $t_0>0$, and let $x$ be a solution of $\ddot x+\frac{\alpha}{t}\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$. Let $W(t)=\frac12\|\dot x(t)\|^2+\Phi(x(t))$ and, for $z\in\mathcal H$, $h_z(t)=\frac12\|x(t)-z\|^2$, so that $\dot h_z(t)=\langle x(t)-z,\dot x(t)\rangle$. Put
--   $$C=\frac1{t_0}\dot h_z(t_0)+(\alpha+1)\frac1{t_0^2}h_z(t_0)+\frac{3}{2\alpha}W(t_0).$$
--   Then for every $t\ge t_0$,
--   $$\int_{t_0}^{t}\frac1s\big(W(s)-\Phi(z)\big)\,ds\le C-\frac1t\dot h_z(t)-\frac{3}{2\alpha}W(t).$$
--
--   This relation between $h_z$ and $W$ is the estimate from which the minimizing property $\lim_{t\to+\infty}\Phi(x(t))=\inf\Phi$ (Theorem 2.3) is derived.
--
--   **Formalization Note** The page states "there is a constant $C$"; the constant above is the one computed at the end of the proof on p. 3, and the statement is given for every $t\ge t_0$ (the proof integrates from $t_0$ to $t>t_0$; at $t=t_0$ it holds trivially). The integral is an ordinary integral over the compact interval $[t_0,t]$ of a continuous function ($W$ is continuous along a solution and $s\ge t_0>0$), so no integrability hypothesis is needed.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 3, Lemma 2.2 and its proof (constant C)

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

namespace InertialAVD.Traj

theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) (z : H) :
    ∀ t ∈ Set.Ici t₀,
      ∫ s in t₀..t, (1 / s) * (energyW Φ x v s - Φ z) ≤
        ((1 / t₀) * inner ℝ (x t₀ - z) (v t₀) + (α + 1) * (1 / t₀ ^ 2) * anchorDist x z t₀
            + (3 / (2 * α)) * energyW Φ x v t₀)
          - (1 / t) * inner ℝ (x t - z) (v t) - (3 / (2 * α)) * energyW Φ x v t := by sorry

end InertialAVD.Traj
