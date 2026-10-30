-- Prove2me | Theorems.Thm_OrabonaOL_OGD_ogd_regret_bound
-- name    : OrabonaOL.OGD.ogd_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:15.146993+00:00
-- url     : https://prove2.me/theorems/f3e448ee-f267-48b6-ac6f-1bcde7c1e56e
-- title:
--   Theorem 2.13 — regret of projected OGD with non-increasing and with constant step sizes
-- statement:
--   Let $V \subseteq \mathbb{R}^d$ be a non-empty closed convex set Let $T \ge 1$ and let $\ell_1, \dots, \ell_T : \mathbb{R}^d \to \mathbb{R}$ be an arbitrary sequence of functions, each convex on $V$ and differentiable on an open set containing $V$. Let the step sizes satisfy $\eta_t > 0$ for $t = 1, \dots, T$ and $\eta_{t+1} \le \eta_t$ for $t = 1, \dots, T-1$. Let $x_1 \in V$ be arbitrary and let $x_1, \dots, x_{T+1}$ be the iterates of Projected Online Gradient Descent (Algorithm 2.1),
--
--   $$
--   g_t = \nabla \ell_t(x_t), \qquad x_{t+1} = \Pi_V(x_t - \eta_t g_t), \qquad t = 1, \dots, T .
--   $$
--
--   Then for every competitor $u \in V$ the following two bounds hold. First, for every real $D$ with $\|x - y\|_2 \le D$ for all $x, y \in V$ (for instance the diameter $D = \sup_{x,y \in V}\|x - y\|_2$ when $V$ is bounded),
--
--   $$
--   \sum_{t=1}^T \bigl(\ell_t(x_t) - \ell_t(u)\bigr) \le \frac{D^2}{2\eta_T} + \sum_{t=1}^T \frac{\eta_t}{2}\|g_t\|_2^2 - \frac{1}{2\eta_T}\|x_{T+1} - u\|_2^2 .
--   $$
--
--   Second, if the step size is constant, $\eta_t = \eta$ for all $t = 1, \dots, T$, then (with no bound $D$ needed, so also for unbounded $V$)
--
--   $$
--   \sum_{t=1}^T \bigl(\ell_t(x_t) - \ell_t(u)\bigr) \le \frac{\|u - x_1\|_2^2}{2\eta} + \frac{\eta}{2}\sum_{t=1}^T \|g_t\|_2^2 - \frac{1}{2\eta}\|x_{T+1} - u\|_2^2 .
--   $$
--
--   The left-hand side is the regret $\mathrm{Regret}_T(u)$ of the algorithm against $u$. This is the basic regret guarantee of Online Gradient Descent with time-varying, non-increasing learning rates on a bounded domain; choosing $\eta_t$ to balance the two main terms yields $O(DL\sqrt{T})$ regret for losses with gradients bounded by $L$. The last, non-positive term is kept because some later arguments use it.
--
--   **Formalization Note** Indices are 1-based; the losses are a sequence $\ell : \mathbb{N} \to (\mathbb{R}^d \to \mathbb{R})$ and the iterates satisfy the predicate `IsProjectedOGDRun`. $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`, $\nabla$ is `gradient`, sums run over `Finset.Icc 1 T`.
--
--   Differences from the source:
--   - generalization: D := sup_{x,y ∈ V} ‖x − y‖₂ (the diameter) → any real D with ‖x − y‖ ≤ D for all x, y ∈ V; reason: the right-hand side is increasing in D ≥ 0, and D = diameter is such a bound when V is bounded; for unbounded V the book's bound is +∞ and has no content. Avoids Metric.diam, which is 0 on unbounded sets
--   - generalization: the loss is convex (on an open set containing V, or on all of R^d) → ConvexOn ℝ V (convexity on V only); reason: a function convex on a convex set containing V is convex on V, so the Lean hypothesis is implied by the book's; the first-order inequality used in the proof only needs convexity along segments inside V
--   - encoding: ℓ_1, …, ℓ_T and η_T for a horizon T → hypothesis 1 ≤ T; reason: at T = 0 there is no step size η_T of the run; the condition only excludes this undefined case
--   - encoding: Π_V(z), the unique argmin of ‖z − y‖₂ over y ∈ V → any p with IsEuclideanProj V z p; reason: for non-empty closed convex V the argmin exists and is unique, so the two describe the same point
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 13 (PDF p. 25), Theorem 2.13, both displayed bounds (proof on pp. 13–14, PDF pp. 25–26); Algorithm 2.1 on p. 12 (PDF p. 24)

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_OrabonaOL_OGD_IsProjectedOGDRun

namespace OrabonaOL.OGD

/-- **Theorem 2.13: regret of projected OGD (non-increasing and constant step sizes).**
Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 13 (PDF p. 25),
Theorem 2.13, both displayed bounds (proof on pp. 13–14, PDF pp. 25–26); Algorithm 2.1 on
p. 12 (PDF p. 24).

Let `V ⊆ ℝ^d` be non-empty, closed and convex, let `ℓ_1, …, ℓ_T` be convex on `V` and
differentiable on an open set containing `V`, let `0 < η_{t+1} ≤ η_t` (and `η_t > 0`), and let
`x_1, …, x_{T+1}` be the iterates of Algorithm 2.1 from any `x_1 ∈ V`, with `g_t = ∇ℓ_t(x_t)`.
Then for every `u ∈ V`:
1. for every `D` with `‖x − y‖₂ ≤ D` for all `x, y ∈ V`,
   `∑_{t=1}^T (ℓ_t(x_t) − ℓ_t(u)) ≤ D²/(2η_T) + ∑_{t=1}^T (η_t/2)‖g_t‖² − ‖x_{T+1} − u‖²/(2η_T)`;
2. if `η_t = η` for all `t = 1, …, T`, then
   `∑_{t=1}^T (ℓ_t(x_t) − ℓ_t(u)) ≤ ‖u − x_1‖²/(2η) + (η/2)∑_{t=1}^T ‖g_t‖² − ‖x_{T+1} − u‖²/(2η)`.

**Formalization Note.** Indices are 1-based and `T ≥ 1`. `D` is any upper bound on the
diameter `sup_{x,y ∈ V} ‖x − y‖₂`; taking `D` equal to the diameter (when `V` is bounded) gives
the book's first bound. The second (constant step size) bound needs no such `D`, so it covers
unbounded `V`, as the book remarks on p. 14. Convexity of `ℓ_t` is required on `V` only. -/
theorem ogd_regret_bound {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (hVne : V.Nonempty) (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ V (ℓ t))
    (hℓdiff : ∀ t ∈ Finset.Icc 1 T, ∃ U : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧ V ⊆ U ∧ DifferentiableOn ℝ (ℓ t) U)
    (η : ℕ → ℝ) (hηpos : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hηmono : ∀ t : ℕ, 1 ≤ t → t + 1 ≤ T → η (t + 1) ≤ η t)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsProjectedOGDRun V η ℓ T x)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) :
    (∀ D : ℝ, (∀ y ∈ V, ∀ z ∈ V, ‖y - z‖ ≤ D) →
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u) ≤
        D ^ 2 / (2 * η T) + ∑ t ∈ Finset.Icc 1 T, η t / 2 * ‖gradient (ℓ t) (x t)‖ ^ 2
          - 1 / (2 * η T) * ‖x (T + 1) - u‖ ^ 2) ∧
    (∀ c : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = c) →
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u) ≤
        ‖u - x 1‖ ^ 2 / (2 * c) + c / 2 * ∑ t ∈ Finset.Icc 1 T, ‖gradient (ℓ t) (x t)‖ ^ 2
          - 1 / (2 * c) * ‖x (T + 1) - u‖ ^ 2) := by sorry

end OrabonaOL.OGD
