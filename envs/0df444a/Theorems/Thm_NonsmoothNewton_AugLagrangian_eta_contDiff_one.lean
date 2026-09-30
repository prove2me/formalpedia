-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_eta_contDiff_one
-- name    : NonsmoothNewton.AugLagrangian.eta_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:04:42.947361+00:00
-- url     : https://prove2.me/theorems/379dfcf4-c224-44c1-97e4-753f60a4a0ed
-- title:
--   The augmented-Lagrangian inequality term $\eta(x,s)=\phi(r,g(x),s)$ is $C^1$ on $\mathbb{R}^n\times\mathbb{R}$
-- statement:
--   Let $r>0$ and let $g:\mathbb{R}^n\to\mathbb{R}$ be $C^1$. For $\eta(x,s)=\phi(r,g(x),s)$ the single inequality term of Rockafellar's augmented Lagrangian, prove that $\eta:\mathbb{R}^n\times\mathbb{R}\to\mathbb{R}$ is continuously differentiable everywhere. Writing $u(x,s)=s+rg(x)$ for the switching function, the two branches of $\phi$ coincide on $u=0$ and satisfy the identity $ya+\frac r2a^2=-\frac1{2r}y^2+\frac1{2r}(y+ra)^2$, so $\eta=-\frac1{2r}s^2+\frac1{2r}\bigl(\max(0,u)\bigr)^2$. The squared positive part of a $C^1$ function is $C^1$, with derivative $2\max(0,u)$, which is continuous. This is the $C^1$ regularity asserted in item 1 of Theorem 4.1 and is a prerequisite for the gradient formulas and their local Lipschitz continuity.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), pp. 363-364, Section 4, proof of Theorem 4.1, item 1 ($\eta \in C^1$); the two branches of $\phi$ and their agreement on the surface $y+ra=0$ are on p. 363.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

namespace NonsmoothNewton.AugLagrangian

/-- Child of `eta_C1_grad_locLip`, first step of Qi-Sun (1993), Section 4, proof of Theorem 4.1,
pp. 363-364. The single inequality term $\eta(x,s)=\phi(r,g(x),s)$ of the augmented Lagrangian is
continuously differentiable on $\mathbb{R}^n\times\mathbb{R}$ whenever $r>0$ and $g$ is $C^1$.

The two branches of $\phi$ agree where $y+ra=0$, since there $y*a+\frac r2a^2=-\frac{r}{2}a^2=-\frac{1}{2r}y^2$.
The exact identity $y a+\frac r2 a^2=-\frac{1}{2r}y^2+\frac{1}{2r}(y+ra)^2$ therefore rewrites the
function as $-\frac{1}{2r}s^2+\frac{1}{2r}(\max 0\,(s+rg(x)))^2$; the squared positive part is $C^1$
(its derivative is the continuous map $z\mapsto 2\max 0\,(s+rg(x))$) though not $C^2$, which is
exactly the regularity the semismoothness argument needs. -/
theorem eta_contDiff_one {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (eta r g) := by sorry

end NonsmoothNewton.AugLagrangian
