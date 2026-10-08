-- Prove2me | Theorems.Thm_OnlineConvexOpt_Regularization_rftl_regret_bound_v2
-- name    : OnlineConvexOpt.Regularization.rftl_regret_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:20.330986+00:00
-- url     : https://prove2.me/theorems/84822fcb-ac25-4c5d-9726-885a8f17290e
-- title:
--   Theorem 5.2 — RFTL regret bound against every comparator $u\in K$ (convex costs, corrected regret)
-- statement:
--   **Statement (Theorem 5.2).** Let $K$ be a nonempty convex decision set in a real Hilbert space, $R$ a regularizer convex on $K$ with gradient map $\nabla R$ on $K$, $\eta>0$, and $f_0,f_1,\dots$ cost functions convex on $K$. Let $(x,\nabla)$ be a run of the RFTL algorithm (Algorithm 13) on $f$ over $K$, and for each $t$ let $\|\nabla_t\|^{*2}_t$ be the squared dual norm of $\nabla_t$ local to the segment $[x_t,x_{t+1}]$ (Definition 5.1, witnessed by `IsLocalDualNormSq`). Then for every horizon $T$ and every $u\in K$,
--   $$\sum_{t=1}^{T}\bigl(f_t(x_t)-f_t(u)\bigr)\;\le\;2\eta\sum_{t=1}^{T}\|\nabla_t\|^{*2}_t+\frac{R(u)-R(x_1)}{\eta}.$$
--
--   **Formalization Note.** The retired statement omitted the OCO standing assumption that the costs are convex on $K$ (the proof's first step, Eq. (5.1), is the convexity inequality $f_t(x_t)-f_t(u)\le\nabla_t^\top(x_t-u)$), and it asserted the bound for the global regret `RegretT` (the supremum over all comparators) with a right-hand side depending on the particular $u$ — false at $u=x_1$ even for linear costs. The new statement adds `hfconv` and states the conclusion as the regret against the fixed comparator $u$, which is what the book proves ("for every $u\in K$", Lemma 5.4) and what its "$\mathrm{Regret}_T\le\dots$ for every $u\in K$" means; the usual $\mathrm{Regret}_T\le 2\eta\sum_t\|\nabla_t\|^{*2}_t+D_R^2/\eta$ follows by taking $u$ to be the best fixed decision. The local dual norm is any witness of `IsLocalDualNormSq` (the bound holds for every such witness); $x_1$ is $x_0$ in the $0$-indexed convention. The file imports the re-issued `OnlineConvexOpt_Regularization_Protocol_v2` (identical except that $D_R^2$ is defined as the real supremum of $\{R(x)-R(y):x,y\in K\}$ instead of nested `⨆` binders) and `OnlineConvexOpt_FirstOrder_Protocol_v2`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 74, Theorem 5.2 (PDF p. 96)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem 5.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 74, PDF p. 96). The RFTL algorithm (Algorithm 13, regularizer `R` with
gradient map `gradR`, convex decision set `K`, step size `η > 0`) run on convex cost functions
`f` attains, for every comparator `u ∈ K`,
`Σ_{t=1}^T (f_t(x_t) - f_t(u)) ≤ 2η Σ_{t=1}^T ‖∇_t‖*²_t + (R(u) - R(x_1))/η`
— the book's "`Regret_T ≤ …` for every `u ∈ K`", i.e. the regret against the fixed comparator
`u`, which is exactly what its proof (Lemma 5.4, "for every `u ∈ K`") establishes. In the
chapter's 0-indexed convention (round `t ∈ ℕ` is the book's round `t + 1`), `‖∇_t‖*²_t` — the
squared dual norm of `∇_t` local to the segment `[x_t, x_{t+1}]` — is `nsq t`, any value
satisfying `IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t)`, and `x_1` is `x 0`.

Corrected version: the retired statement dropped the OCO standing assumption that the costs
`f_t` are convex on `K` (the proof's first step, Eq. (5.1), is the convexity inequality
`f_t(x_t) - f_t(u) ≤ ∇_t^⊤(x_t - u)`), and it bounded the global regret `RegretT` (the supremum
over all comparators) by a right-hand side depending on the particular `u`, which is false at
`u = x_1`; the conclusion is now the per-comparator inequality the book proves. -/
theorem rftl_regret_bound_v2
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (R : E → ℝ) (hRconv : ConvexOn ℝ K R) (gradR : E → E)
    (hgradR : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (nsq : ℕ → ℝ) (hnsq : ∀ t, IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t))
    (T : ℕ) (u : E) (hu : u ∈ K) :
    (∑ t ∈ Finset.range T, (f t (x t) - f t u)) ≤
      2 * η * (∑ t ∈ Finset.range T, nsq t) + (R u - R (x 0)) / η := by sorry

end OnlineConvexOpt.Regularization
