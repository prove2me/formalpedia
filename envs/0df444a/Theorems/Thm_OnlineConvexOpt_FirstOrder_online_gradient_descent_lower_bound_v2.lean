-- Prove2me | Theorems.Thm_OnlineConvexOpt_FirstOrder_online_gradient_descent_lower_bound_v2
-- name    : OnlineConvexOpt.FirstOrder.online_gradient_descent_lower_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:52.81873+00:00
-- url     : https://prove2.me/theorems/206a3610-213c-4abc-b6c8-a2c2bf0eff30
-- title:
--   Theorem 3.2 — Ω(DG√T) worst-case regret lower bound (corrected regret definition, Lipschitz costs)
-- statement:
--   **Statement (Theorem 3.2).** Any algorithm for online convex optimization incurs $\Omega(DG\sqrt T)$ regret in the worst case. Formally: there is an absolute constant $c>0$ such that for every dimension $n\ge1$ there is a convex, complete, nonempty decision set $K\subseteq\mathbb R^n$ of diameter at most $D>0$ and a constant $G>0$ such that, for every non-anticipating algorithm $A$ playing in $K$ and every horizon $T\ge1$, there is a cost sequence $f$ — each $f_t$ convex on $K$, $G$-Lipschitz on $K$ and with every gradient at a point of $K$ of norm at most $G$ (the chapter's standing assumption "$G$ bounds the (sub)gradient norms over $K$", p. 20) — chosen after $A$ and $T$, against which $A$'s regret is at least $c\,DG\sqrt T$.
--
--   **Formalization Note.** The retired statement was *proved* only through two junk routes: its regret `RegretT` (from `OnlineConvexOpt_FirstOrder_Protocol`) returned the junk value $0$ for the comparator term outside $K$, so constant costs on $K=\{0\}$ gave "regret" $T\sqrt T$; and its only constraint on the adversary's costs was a bound on gradients *where they exist*, which is vacuous for costs with no gradient on $K$. The new statement imports `OnlineConvexOpt_FirstOrder_Protocol_v2` (`RegretT` subtracts the real infimum of the cumulative cost over $K$; genuine here since $K$ is nonempty and bounded and the costs are Lipschitz on $K$) and requires the adversary's costs to be $G$-Lipschitz on $K$ in addition to convex with $G$-bounded gradients, exactly the class the book's hard instance (linear costs $v^\top x$ on the hypercube) belongs to. The quantifier order (instance, then algorithm and horizon, then costs) is unchanged; the parenthetical "even for costs drawn from a fixed stationary distribution" is not formalized, as before.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 45, Theorem 3.2 (PDF p. 67)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.FirstOrder

/-- Theorem 3.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 45, PDF p. 67). Any online algorithm for online convex optimization
incurs `Ω(DG√T)` regret in the worst case: for every dimension `n` there is a decision set `K`
(convex, complete, nonempty, diameter `≤ D`) such that **for every** non-anticipating algorithm
`A` playing in `K` and every horizon `T ≥ 1`, there is a cost sequence `f` (chosen against `A`)
satisfying the chapter's standing assumptions — each `f_t` convex on `K`, `G`-Lipschitz on `K`
and with every gradient at a point of `K` of norm `≤ G` (book p. 20: `G` bounds the subgradient
norms over `K`, which implies `G`-Lipschitzness) — forcing regret at least `c · D · G · √T`,
for an absolute constant `c > 0`. The quantifier order is load-bearing: the cost sequence is
chosen *after* the algorithm and the horizon. (The parenthetical strengthening "even if the cost
functions are generated from a fixed stationary distribution" is not captured here.)

Corrected version: `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret (genuine
infimum over `K`; the retired one returned the junk value `0` outside `K`, which let constant
costs on a singleton `K` "prove" the bound), and the adversary's costs must be `G`-Lipschitz on
`K` and not merely have `G`-bounded gradients where differentiable (the retired hypothesis was
vacuous for costs that are nowhere differentiable on `K`, e.g. on a `K` with empty interior). -/
theorem online_gradient_descent_lower_bound_v2 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (D G : ℝ), 0 < D ∧ 0 < G ∧
        Convex ℝ K ∧ IsComplete K ∧ K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) ∧
        ∀ (A : (ℕ → EuclideanSpace ℝ (Fin n) → ℝ) → ℕ → EuclideanSpace ℝ (Fin n)),
          IsOnlineAlgorithm K A →
          ∀ T : ℕ, 1 ≤ T →
            ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
              (∀ t, ConvexOn ℝ K (f t)) ∧
              (∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y) ∧
              (∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G) ∧
              c * D * G * Real.sqrt T ≤ RegretT K f (fun t => A f t) T := by sorry

end OnlineConvexOpt.FirstOrder
