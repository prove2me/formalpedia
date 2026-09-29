-- Prove2me | Theorems.Thm_OnlineConvexOpt_Regularization_rftl_regret_bound
-- name    : OnlineConvexOpt.Regularization.rftl_regret_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:36:52.552005+00:00
-- url     : https://prove2.me/theorems/2b860017-70cd-47cc-93fb-d47c5b0f4b84
-- title:
--   Theorem 5.2 — RFTL regret bound
-- statement:
--   **Statement (Theorem 5.2).** Let $K$ be a nonempty convex decision set in a real Hilbert space, $R : K \to \mathbb{R}$ a convex regularizer with gradient map $\mathrm{gradR}$, $\eta > 0$ a step size, $f$ a sequence of convex cost functions, and $(x, \mathrm{grad})$ a run of the RFTL algorithm (Algorithm 13) on $f$ over $K$. Then for every horizon $T$ and every $u \in K$,
--   $$\mathrm{Regret}_T \;\le\; 2\eta \sum_{t=1}^{T} \|\nabla_t\|^{*2}_t \;+\; \frac{R(u) - R(x_1)}{\eta},$$
--   where $\|\nabla_t\|^{*2}_t$ is the squared dual norm of $\nabla_t$ local to the segment $[x_t, x_{t+1}]$ (Definition 5.1).
--
--   This is the chapter's main result: the RFTL meta-algorithm, run with *any* admissible regularizer $R$, attains a regret bound governed by the cumulative squared local dual norm of the gradients and the regularizer's range over $K$. Its proof (Lemma 5.3 plus a generalized Cauchy-Schwarz argument bounding the prediction-drift term by $2\eta\|\nabla_t\|^{*2}_t$) is the content this mission's milestones supply.
--
--   **Formalization Note.** $x_1$ is $x_0$ under this chapter's 0-indexed shift. $\|\nabla_t\|^{*2}_t$ is any value `nsq t` witnessing `IsLocalDualNormSq R gradR (x t) (x (t+1)) (grad t) (nsq t)`; the theorem is stated for an arbitrary such witness, matching the book's use of the local norm as a well-defined quantity rather than a specific formula. The further corollary the book states immediately after Theorem 5.2 (an upper bound $\mathrm{Regret}_T \le 2D_RG_R\sqrt{2T}$ under a uniform bound $\|\nabla_t\|^*_t \le G_R$) is a separate, unnumbered statement and is not formalized here, per this series' convention of formalizing only numbered results.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 74, Theorem 5.2 (PDF p. 96)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem 5.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 74, PDF p. 96). The RFTL algorithm (Algorithm 13, regularizer `R` with
gradient map `gradR`, convex decision set `K`, step size `η`) attains, for every `u ∈ K`,
`Regret_T ≤ 2η Σ_{t=1}^T ‖∇_t‖*²_t + (R(u) - R(x_1))/η`. In the chapter's 0-indexed convention
(round `t ∈ ℕ` is the book's round `t + 1`), `‖∇_t‖*²_t` — the squared dual norm of `∇_t` local
to the segment `[x_t, x_{t+1}]` — is `nsq t`, any value satisfying `IsLocalDualNormSq R gradR
(x t) (x (t + 1)) (grad t) (nsq t)`, and `x_1` is `x 0`. -/
theorem rftl_regret_bound
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (R : E → ℝ) (hRconv : ConvexOn ℝ K R) (gradR : E → E)
    (hgradR : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad)
    (nsq : ℕ → ℝ) (hnsq : ∀ t, IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t))
    (T : ℕ) (u : E) (hu : u ∈ K) :
    RegretT K f x T ≤
      2 * η * (∑ t ∈ Finset.range T, nsq t) + (R u - R (x 0)) / η := by sorry

end OnlineConvexOpt.Regularization
