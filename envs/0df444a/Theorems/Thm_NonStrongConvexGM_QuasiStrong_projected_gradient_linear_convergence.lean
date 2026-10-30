-- Prove2me | Theorems.Thm_NonStrongConvexGM_QuasiStrong_projected_gradient_linear_convergence
-- name    : NonStrongConvexGM.QuasiStrong.projected_gradient_linear_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:40:38.119371+00:00
-- url     : https://prove2.me/theorems/f7d347fd-051f-4b40-b41e-dc2c9931aac3
-- title:
--   Theorem 11 — Projected gradient linear convergence under quasi-strong convexity
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f:X\to\mathbb R$ be convex with an attained finite minimum, and let $g$ represent its derivative within $X$, with $\|g(x)-g(y)\|\le L\|x-y\|$ for $x,y\in X$ and $L>0$. Write $X^*=\operatorname{argmin}_{x\in X}f(x)$, $f^*=\min_{x\in X}f(x)$ and $\bar x=[x]_{X^*}$ for the exact nearest optimizer. The classes $S,qS,G,U,F$ use equations (7a), (10), (17), (13), (22), respectively, with the same positive constant $\kappa$ and this common smooth convex setting.
--
--   Assume $f\in qS_{L,\kappa}(X)$ and choose any $x^0\in X$. Generate $x^{k+1}=[x^k-L^{-1}g(x^k)]_X$ for every natural $k$. Put $\bar x^k=[x^k]_{X^*}$ and $\mu=\kappa/L$. Then
--
--   $$\|x^k-\bar x^k\|^2\le\left(\frac{1-\mu}{1+\mu}\right)^k\|x^0-\bar x^0\|^2\quad(k\in\mathbb N).$$
--
--   In addition, there exist one $x^\infty\in X^*$ and constants $C\ge0$, $0\le r<1$ such that
--
--   $$x^k\longrightarrow x^\infty,\qquad \|x^k-x^\infty\|\le Cr^k\quad(k\in\mathbb N).$$
--
--   The whole sequence converges to this one point. The exact factor bounds squared distance to the optimizer set; no equality $x^\infty=\bar x^0$ or prescribed rate for error to that fixed point is imposed. The result includes all closed convex feasible sets and nonunique minimizers.
--
--   **Formalization Note** The $k=0$ inequality is included, with $0^0=1$. At $\mu=1$ the first iterate is optimal. No assumption $\kappa\le L$ or $\mu<1$ is added. If every feasible point is optimal, $\kappa>L$ is allowed and both distances in the signed-factor estimate are zero.
--
--   Differences from the source:
--   - generalization: a classical smooth objective with its ambient gradient on X → an ambient representative f with a supplied field g representing its Fréchet derivative within X and the same on-domain L-Lipschitz bound; reason: every classical ambient-gradient instance satisfies this model; no off-domain regularity is imposed, including at boundaries and on lower-dimensional feasible sets
--   - encoding: an attained minimum and Euclidean projections onto the feasible and optimal sets → the published actual argmin and nearest-point predicate, the value at a chosen actual optimizer, and exact nearest-point selection; reason: all optimizers have the same value and nearest points on the nonempty closed convex sets used are unique; invalid-set projection defaults are unreachable
--   - encoding: Euclidean space R^n → EuclideanSpace over real scalars indexed by Fin n for arbitrary natural n; reason: the Euclidean norm and inner product are unchanged; dimension zero is harmless
--   - reading: the GM box specifies x⁰ but prints k ≥ 1 for the update of xᵏ⁺¹ → the recurrence executes its first update at k = 0 and every natural k thereafter; reason: the initial-point estimate (45) and its proof require a determined first iterate x¹
--   - encoding: the sequence converges linearly to some optimal point, in addition to (45) → one optimal limit, whole-sequence Tendsto, and constants C ≥ 0 and 0 ≤ r < 1 bounding norm error by C rᵏ for every natural k; reason: this spells out R-linear point convergence separately from the exact squared-distance-to-set estimate; no explicit rate to the fixed limit is imposed
-- source:
--   Necoara, Nesterov & Glineur, arXiv:1504.06298v4 (9 August 2016), https://arxiv.org/abs/1504.06298v4, Theorem 11, p. 19, PDF p. 19; (45), §5.1 GM; proof pp. 20–21 (PDF pp. 20–21).

import Definitions.Def_NonStrongConvexGM_QuasiStrong_Model

namespace NonStrongConvexGM.QuasiStrong

theorem projected_gradient_linear_convergence {n : ℕ} (P : Problem n) (κ : ℝ) (h : IsQuasiStrong P κ)
    (x₀ : NecoaraNG.Chain.E n) (hx₀ : x₀ ∈ P.X) :
    (∀ k : ℕ, ‖orbit P x₀ k - nearestOpt P (orbit P x₀ k)‖ ^ 2 ≤
      rate P κ ^ k * ‖x₀ - nearestOpt P x₀‖ ^ 2) ∧
    (∃ xlim : NecoaraNG.Chain.E n, xlim ∈ NecoaraNG.Chain.optSet P.X P.f ∧
      Filter.Tendsto (orbit P x₀) Filter.atTop (nhds xlim) ∧
      ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
        ∀ k : ℕ, ‖orbit P x₀ k - xlim‖ ≤ C * r ^ k) := by sorry

end NonStrongConvexGM.QuasiStrong
