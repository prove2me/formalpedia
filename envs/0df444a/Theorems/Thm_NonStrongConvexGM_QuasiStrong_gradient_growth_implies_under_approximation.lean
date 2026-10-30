-- Prove2me | Theorems.Thm_NonStrongConvexGM_QuasiStrong_gradient_growth_implies_under_approximation
-- name    : NonStrongConvexGM.QuasiStrong.gradient_growth_implies_under_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:21.169993+00:00
-- url     : https://prove2.me/theorems/0e573bdd-0a11-48f4-b15e-03d54d1e1701
-- title:
--   Theorem 3 — Quadratic gradient growth implies quadratic under-approximation
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f:X\to\mathbb R$ be convex with an attained finite minimum, and let $g$ represent its derivative within $X$, with $\|g(x)-g(y)\|\le L\|x-y\|$ for $x,y\in X$ and $L>0$. Write $X^*=\operatorname{argmin}_{x\in X}f(x)$, $f^*=\min_{x\in X}f(x)$ and $\bar x=[x]_{X^*}$ for the exact nearest optimizer. The classes $S,qS,G,U,F$ use equations (7a), (10), (17), (13), (22), respectively, with the same positive constant $\kappa$ and this common smooth convex setting.
--
--   If $f\in G_{L,\kappa}(X)$, then
--
--   $$f(x)\ge f^*+\langle g(\bar x),x-\bar x\rangle+\frac\kappa2\|x-\bar x\|^2\quad(x\in X).$$
--
--   Thus $f\in U_{L,\kappa}(X)$ with the original constant. The constrained optimizer's gradient term is retained and need not vanish.
--
--   Differences from the source:
--   - generalization: a classical smooth objective with its ambient gradient on X → an ambient representative f with a supplied field g representing its Fréchet derivative within X and the same on-domain L-Lipschitz bound; reason: every classical ambient-gradient instance satisfies this model; no off-domain regularity is imposed, including at boundaries and on lower-dimensional feasible sets
--   - encoding: an attained minimum and Euclidean projections onto the feasible and optimal sets → the published actual argmin and nearest-point predicate, the value at a chosen actual optimizer, and exact nearest-point selection; reason: all optimizers have the same value and nearest points on the nonempty closed convex sets used are unique; invalid-set projection defaults are unreachable
--   - encoding: Euclidean space R^n → EuclideanSpace over real scalars indexed by Fin n for arbitrary natural n; reason: the Euclidean norm and inner product are unchanged; dimension zero is harmless
-- source:
--   Necoara, Nesterov & Glineur, arXiv:1504.06298v4 (9 August 2016), https://arxiv.org/abs/1504.06298v4, Theorem 3, p. 8, PDF p. 8

import Definitions.Def_NonStrongConvexGM_QuasiStrong_Model

namespace NonStrongConvexGM.QuasiStrong

theorem gradient_growth_implies_under_approximation {n : ℕ} (P : Problem n) (κ : ℝ) (h : GradientGrowth P κ) : UnderApprox P κ := by sorry

end NonStrongConvexGM.QuasiStrong
