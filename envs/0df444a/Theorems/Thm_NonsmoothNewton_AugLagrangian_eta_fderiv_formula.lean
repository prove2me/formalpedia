-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_eta_fderiv_formula
-- name    : NonsmoothNewton.AugLagrangian.eta_fderiv_formula
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T23:04:57.077883+00:00
-- url     : https://prove2.me/theorems/a6869330-b691-4c37-b6a2-3f79ab48c007
-- title:
--   The gradient of $\eta$: $\nabla\eta(x,s)=((s+rg(x))\nabla g(x),\ g(x))$ where $s+rg(x)\ge 0$ and $(0,-s/r)$ where $s+rg(x)\le 0$
-- statement:
--   Let $r>0$ and $g:\mathbb{R}^n\to\mathbb{R}$ be $C^2$, and assume $\eta$ is $C^1$. Then the gradient of $\eta$ at $(x,s)$ is $\bigl((s+rg(x))\nabla g(x),\,g(x)\bigr)$ where $s+rg(x)\ge 0$, and $\bigl(0,\,-\frac sr\bigr)$ where $s+rg(x)\le 0$. On the open regions $s+rg(x)>0$ and $s+rg(x)<0$ the function $\eta$ is the polynomial $s\,g(x)+\frac r2 g(x)^2$ and respectively $-\frac1{2r}s^2$, whose differentials are the displayed expressions; continuity of $\nabla\eta$ supplied by $C^1$ extends the identity across the surface $s+rg(x)=0$, and there the two formulas coincide because $g(x)=-s/r$. This is the displayed gradient formula, item 2 of Theorem 4.1.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), pp. 363-364, Section 4, proof of Theorem 4.1, the display of $\nabla\eta$ (item 2 of the theorem).

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

namespace NonsmoothNewton.AugLagrangian

/-- Child of `eta_C1_grad_locLip`, second step of Qi-Sun (1993), Section 4, proof of Theorem 4.1,
pp. 363-364: the displayed formula for $\nabla\eta$ (item 2 of the theorem).

The gradient is represented by the Fréchet derivative, a continuous linear functional on
$\mathbb{R}^n\times\mathbb{R}$: in the first case $(h,\alpha)\mapsto (s+rg(x))\,Dg(x)h+g(x)\,\alpha$,
and in the second $(h,\alpha)\mapsto -\frac sr\,\alpha$. The two agree where $s+rg(x)=0$, because
there $g(x)=-\frac sr$, so the two non-strict cases are consistent. -/
theorem eta_fderiv_formula {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (hη : ContDiff ℝ 1 (eta r g)) :
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, 0 ≤ z.2 + r * g z.1 →
      fderiv ℝ (eta r g) z =
        (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
            (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
          + g z.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, z.2 + r * g z.1 ≤ 0 →
      fderiv ℝ (eta r g) z =
        (-(z.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) := by sorry

end NonsmoothNewton.AugLagrangian
