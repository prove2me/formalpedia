-- Prove2me | Theorems.Thm_MarkmanSecant_exp_secant_plane_in_hodge_ring
-- name    : MarkmanSecant.exp_secant_plane_in_hodge_ring
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T15:04:02.217747+00:00
-- url     : https://prove2.me/theorems/a39a0282-0c88-48b3-ba7c-dd303bc164dc
-- title:
--   Equation (2.4.5): $\operatorname{Re}\exp(u)$ and $\operatorname{Im}\exp(u)/\sqrt d$ lie in the Hodge ring
-- statement:
--   **Equation (2.4.5) of Markman, arXiv:2502.03415: the plane $P$ lies in the Hodge ring.**
--
--   Let $X$ be a complex torus of dimension $n$ with complex structure $J$ ($J^2=-1$), let $\Theta\in H^{1,1}(X,\mathbb{Z})$ be an ample class, let $d$ be a positive integer and $\sqrt{-d}=i\sqrt d$. Then there exist $a,b$ in the Hodge ring $\bigoplus_{p}H^{p,p}(X,\mathbb{Q})$ such that
--   $$\exp(\sqrt{-d}\,\Theta)=a+\sqrt{-d}\,b,\qquad \exp(-\sqrt{-d}\,\Theta)=a-\sqrt{-d}\,b.$$
--
--   Thus $a=\operatorname{Re}\exp(u)$ and $b=\operatorname{Im}\exp(u)/\sqrt d$ span the rational plane $P$ of (2.4.5), $P$ is contained in the Hodge ring, and $\mathbb{P}(P)$ passes through the two conjugate points $[\exp(u)]$, $[\exp(\bar u)]$ defined over $K=\mathbb{Q}(\sqrt{-d})$. This is the Hodge-ring part of Assumption 2.4.1 for the example of §2.4.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem exp_secant_plane_in_hodge_ring (n : ℕ) (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hJ : J * J = -1) (Θ : Spinor n) (hΘ : IsAmpleClass J Θ) (d : ℕ) (hd : 0 < d) :
    ∃ a b : Spinor n, IsInHodgeRing J a ∧ IsInHodgeRing J b ∧
      expS (sqrtNeg d • Θ) = a + sqrtNeg d • b ∧
      expS ((-sqrtNeg d) • Θ) = a - sqrtNeg d • b := by sorry

end MarkmanSecant
