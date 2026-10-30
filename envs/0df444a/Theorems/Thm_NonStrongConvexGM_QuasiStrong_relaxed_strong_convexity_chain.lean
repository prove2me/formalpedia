-- Prove2me | Theorems.Thm_NonStrongConvexGM_QuasiStrong_relaxed_strong_convexity_chain
-- name    : NonStrongConvexGM.QuasiStrong.relaxed_strong_convexity_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:56.293249+00:00
-- url     : https://prove2.me/theorems/9507ae2d-4cc1-4c54-b953-7e86ab3bbc12
-- title:
--   Theorem 4 — Full chain of relaxed strong convexity implications
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f:X\to\mathbb R$ be convex with an attained finite minimum, and let $g$ represent its derivative within $X$, with $\|g(x)-g(y)\|\le L\|x-y\|$ for $x,y\in X$ and $L>0$. Write $X^*=\operatorname{argmin}_{x\in X}f(x)$, $f^*=\min_{x\in X}f(x)$ and $\bar x=[x]_{X^*}$ for the exact nearest optimizer. The classes $S,qS,G,U,F$ use equations (7a), (10), (17), (13), (22), respectively, with the same positive constant $\kappa$ and this common smooth convex setting.
--
--   The full chain, preserving the same $L$, $\kappa$, $X$, $f$ and $g$, is
--
--   $$S_{L,\kappa}(X)\subseteq qS_{L,\kappa}(X)\subseteq G_{L,\kappa}(X)\subseteq U_{L,\kappa}(X)\subseteq F_{L,\kappa}(X).$$
--
--   The statement includes all four adjacent implications. It also retains the equivalence of the first-order definition of $S$ with both source conditions: the Jensen inequality (5) for every $x,y\in X$, $a\in[0,1]$, and the gradient inequality (7b). These read
--
--   $$f(ax+(1-a)y)\le af(x)+(1-a)f(y)-\frac\kappa2a(1-a)\|x-y\|^2,$$
--   $$\kappa\|x-y\|^2\le\langle g(x)-g(y),x-y\rangle.$$
--
--   This retains the original meaning of strong convexity in the complete relaxation hierarchy.
--
--   Differences from the source:
--   - generalization: a classical smooth objective with its ambient gradient on X → an ambient representative f with a supplied field g representing its Fréchet derivative within X and the same on-domain L-Lipschitz bound; reason: every classical ambient-gradient instance satisfies this model; no off-domain regularity is imposed, including at boundaries and on lower-dimensional feasible sets
--   - encoding: an attained minimum and Euclidean projections onto the feasible and optimal sets → the published actual argmin and nearest-point predicate, the value at a chosen actual optimizer, and exact nearest-point selection; reason: all optimizers have the same value and nearest points on the nonempty closed convex sets used are unique; invalid-set projection defaults are unreachable
--   - encoding: Euclidean space R^n → EuclideanSpace over real scalars indexed by Fin n for arbitrary natural n; reason: the Euclidean norm and inner product are unchanged; dimension zero is harmless
--   - encoding: the S class defined by (5), equivalently either condition (7), followed by the chain in Theorem 4 → the first-order S predicate together with its equivalences to (5) and (7b), and every adjacent implication; reason: the source equivalences from pp. 3–4 are retained explicitly rather than assumed silently
-- source:
--   Necoara, Nesterov & Glineur, arXiv:1504.06298v4 (9 August 2016), https://arxiv.org/abs/1504.06298v4, Theorem 4, p. 9, PDF p. 9; §2, pp. 3–4 (PDF pp. 3–4), equivalences (5), (7); (23).

import Definitions.Def_NonStrongConvexGM_QuasiStrong_Model

namespace NonStrongConvexGM.QuasiStrong

theorem relaxed_strong_convexity_chain {n : ℕ} (P : Problem n) (κ : ℝ) :
    (Strong P κ ↔ StrongJensen P κ) ∧
    (Strong P κ ↔ StrongMonotone P κ) ∧
    (Strong P κ → IsQuasiStrong P κ) ∧
    (IsQuasiStrong P κ → GradientGrowth P κ) ∧
    (GradientGrowth P κ → UnderApprox P κ) ∧
    (UnderApprox P κ → FunctionalGrowth P κ) := by sorry

end NonStrongConvexGM.QuasiStrong
