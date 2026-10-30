-- Prove2me | Theorems.Thm_NonStrongConvexGM_QuasiStrong_quasi_strong_implies_under_approximation
-- name    : NonStrongConvexGM.QuasiStrong.quasi_strong_implies_under_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:10.011384+00:00
-- url     : https://prove2.me/theorems/359dc9ad-babd-4d68-8d1c-f5bc60f9319d
-- title:
--   Theorem 1 — Quasi-strong convexity implies quadratic under-approximation
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f:X\to\mathbb R$ be convex with an attained finite minimum, and let $g$ represent its derivative within $X$, with $\|g(x)-g(y)\|\le L\|x-y\|$ for $x,y\in X$ and $L>0$. Write $X^*=\operatorname{argmin}_{x\in X}f(x)$, $f^*=\min_{x\in X}f(x)$ and $\bar x=[x]_{X^*}$ for the exact nearest optimizer. The classes $S,qS,G,U,F$ use equations (7a), (10), (17), (13), (22), respectively, with the same positive constant $\kappa$ and this common smooth convex setting.
--
--   If $f\in qS_{L,\kappa}(X)$, then
--
--   $$f(x)\ge f^*+\langle g(\bar x),x-\bar x\rangle+\frac\kappa2\|x-\bar x\|^2\quad(x\in X).$$
--
--   Thus $f\in U_{L,\kappa}(X)$ with the original constant. This relates the inequality directed toward the optimizer to a quadratic approximation based at it.
--
--   Differences from the source:
--   - generalization: a classical smooth objective with its ambient gradient on X → an ambient representative f with a supplied field g representing its Fréchet derivative within X and the same on-domain L-Lipschitz bound; reason: every classical ambient-gradient instance satisfies this model; no off-domain regularity is imposed, including at boundaries and on lower-dimensional feasible sets
--   - encoding: an attained minimum and Euclidean projections onto the feasible and optimal sets → the published actual argmin and nearest-point predicate, the value at a chosen actual optimizer, and exact nearest-point selection; reason: all optimizers have the same value and nearest points on the nonempty closed convex sets used are unique; invalid-set projection defaults are unreachable
--   - encoding: Euclidean space R^n → EuclideanSpace over real scalars indexed by Fin n for arbitrary natural n; reason: the Euclidean norm and inner product are unchanged; dimension zero is harmless
-- source:
--   Necoara, Nesterov & Glineur, arXiv:1504.06298v4 (9 August 2016), https://arxiv.org/abs/1504.06298v4, Theorem 1, p. 6, PDF p. 6

import Definitions.Def_NonStrongConvexGM_QuasiStrong_Model

namespace NonStrongConvexGM.QuasiStrong

theorem quasi_strong_implies_under_approximation {n : ℕ} (P : Problem n) (κ : ℝ) (h : IsQuasiStrong P κ) : UnderApprox P κ := by sorry

end NonStrongConvexGM.QuasiStrong
