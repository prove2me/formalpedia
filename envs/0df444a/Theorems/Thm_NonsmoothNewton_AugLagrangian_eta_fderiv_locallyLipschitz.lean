-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_eta_fderiv_locallyLipschitz
-- name    : NonsmoothNewton.AugLagrangian.eta_fderiv_locallyLipschitz
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T23:04:41.452142+00:00
-- url     : https://prove2.me/theorems/e527b759-84b3-49d0-bb3a-a934132e239b
-- title:
--   The gradient $\nabla\eta$ of the augmented-Lagrangian inequality term is locally Lipschitz
-- statement:
--   Let $r>0$ and $g:\mathbb{R}^n\to\mathbb{R}$ be $C^2$, and assume $\eta(x,s)=\phi(r,g(x),s)$ is $C^1$. Then the map $(x,s)\mapsto D\eta(x,s)$, valued in the continuous linear functionals on $\mathbb{R}^n\times\mathbb{R}$ and measured in operator norm, is locally Lipschitz on $\mathbb{R}^n\times\mathbb{R}$. On the two open regions separated by the surface $s+rg(x)=0$ this map equals the two smooth expressions $((s+rg(x))Dg(x),\,g(x))$ and $(0,\,-\frac sr)$; these agree on the surface because $g(x)=-s/r$ there, and both are smooth there because $Dg$ is continuous. This is the local Lipschitz continuity of $\nabla\eta$ asserted in item 3 of Theorem 4.1, the regularity that makes the semismooth Newton method applicable.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), pp. 363-364, Section 4, proof of Theorem 4.1, the sentence following the display of $\nabla\eta$ (item 3 of the theorem).

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

namespace NonsmoothNewton.AugLagrangian

/-- Child of `eta_C1_grad_locLip`, third step of Qi-Sun (1993), Section 4, proof of Theorem 4.1,
pp. 363-364: $\nabla\eta$ is locally Lipschitz (item 3 of the theorem, the sentence following the
display of the gradient).

The gradient is viewed as a linear functional and bounded in operator norm. Since $g$ is $C^2$,
$\nabla g=fderiv\ \mathbb{R}\ g$ is $C^1$ and therefore locally Lipschitz, and the gradient of $\eta$
differs from the continuous function $(x,s)\mapsto g(x)$ by the term $(s+rg(x))\cdot\Psi$ whose
factor $\Psi$ is bounded on bounded sets. -/
theorem eta_fderiv_locallyLipschitz {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (hη : ContDiff ℝ 1 (eta r g)) :
    LocallyLipschitz (fun z => fderiv ℝ (eta r g) z) := by sorry

end NonsmoothNewton.AugLagrangian
