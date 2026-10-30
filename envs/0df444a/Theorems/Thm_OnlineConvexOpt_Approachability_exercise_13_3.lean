-- Prove2me | Theorems.Thm_OnlineConvexOpt_Approachability_exercise_13_3
-- name    : OnlineConvexOpt.Approachability.exercise_13_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:38.459458+00:00
-- url     : https://prove2.me/theorems/ffc31546-a291-4305-8004-29e2c160895b
-- title:
--   Exercise 13.3: Blackwell's condition is necessary (corrected: payoff u bi-affine)
-- statement:
--   Let $\mathcal K_1\subseteq\mathbb R^n$ and $\mathcal K_2\subseteq\mathbb R^m$ be bounded, closed and convex, let $u$ be bi-affine on $\mathcal K_1\times\mathcal K_2$, and let $S\subseteq\mathbb R^d$ be nonempty, bounded, closed and convex. If $S$ is approachable, then there is an oracle $\mathcal O:\mathbb R^m\to\mathbb R^n$ with
--
--   $$
--   \mathcal O(y)\in\mathcal K_1\quad\text{and}\quad u(\mathcal O(y),y)\in S\qquad\text{for every } y\in\mathcal K_2 .
--   $$
--
--   This is the necessity half of Blackwell's theorem: if some response $y$ of the column player admits no feasible best response, then no algorithm can drive the average payoff to $S$.
--
--   **Formalization Note** Approachability is taken in the per-sequence sense (`IsApproachable`), which is implied by uniform approachability, so the statement covers both readings.
--
--   Differences from the source:
--   - correction: Definition 13.2 puts no condition on the payoff u → hypothesis IsBiaffineOn K₁ K₂ u (u preserves convex combinations in each argument on K₁ × K₂); reason: the printed statement is false for arbitrary continuous u: with K₁ = K₂ = [0,1], S = {0}, u(x,y) = (x − y)², the condition holds but the adversary y_t = 1 if x_t < 1/2, else 0, keeps every payoff ≥ 1/4; with K₁ = K₂ = [0,1], S = {(0,0)}, u(x,y) = (cos πx, sin πx), the condition fails but alternating x_t = 0, 1 gives averages within 1/T of S. Bi-affinity is the hypothesis of the chapter's source (Abernethy–Bartlett–Hazan 2011) and holds for the mixed extension of Definition 13.1
--   - generalization: ∀ y ∈ ∆_m (the finite game of Definition 13.1) → ∀ y ∈ K₂, a bounded closed convex set (Definition 13.2); reason: ∆_m with the bilinear mixed extension u is an instance
--   - generalization: S approachable → S approachable in the per-sequence sense (IsApproachable); reason: uniform approachability implies it, so the hypothesis is the weaker reading
--   - encoding: an oracle O (a row strategy for each y) → O : ℝ^m → ℝ^n with O y ∈ K₁ for y ∈ K₂; reason: an oracle answers with a strategy of the row player, which lies in K₁
--   - encoding: S closed, bounded and convex, with Dist(w,S) = min over S → additionally S.Nonempty; reason: a min over the empty set is undefined; Lean's Metric.infDist w ∅ = 0 would make ∅ approachable
--   - encoding: an algorithm x_t ← A(y_1, …, y_{t−1}), rounds t = 1, …, T, Dist the min over S → a deterministic A t (y₀, …, y_{t−1}) ∈ K₁ on K₂-histories, rounds 0-indexed, average (1/T)∑_{t<T}, Dist = Metric.infDist; reason: the same objects; infDist equals the printed min for nonempty closed S
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Chapter 13, Exercise 3, p. 218 (PDF p. 240)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsBiaffineOn
import Definitions.Def_OnlineConvexOpt_Approachability_IsApproachable

namespace OnlineConvexOpt.Approachability

/-- **Exercise 13.3 (necessity of Blackwell's condition).**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Chapter 13,
Exercise 3, p. 218: "Prove that Blackwell’s condition is necessary, i.e., prove that for a set S
to be approachable in a given vector game, there must exist an oracle O such that
∀y ∈ ∆m , u(O(y), y) ∈ S."

For bounded closed convex `K₁, K₂`, a payoff `u` bi-affine on `K₁ × K₂`, and a nonempty bounded
closed convex `S`: if `S` is approachable (per-sequence reading), then there is an oracle
`O : ℝ^m → ℝ^n` with `O(y) ∈ K₁` and `u(O(y), y) ∈ S` for every `y ∈ K₂`.

**Formalization Note.**
* Generalization: the exercise's `∆_m` (the column player's mixed strategies of Definition 13.1)
  is the generalized decision set `K₂` of Definition 13.2; `K₂ = ∆_m` with the mixed extension
  `u` is the printed case. The oracle's outputs are required to lie in `K₁` (the oracle is a
  best response of the row player).
* The hypothesis is the per-sequence `IsApproachable` (Reading R1-P), the weaker of the two
  readings, so the statement also covers uniform approachability.
* Correction: `u` bi-affine on `K₁ × K₂` (`IsBiaffineOn`); without it the statement is false
  (`K₁ = K₂ = [0,1]`, `S = {(0,0)}`, `u(x, y) = (cos πx, sin πx)`: alternating `x_t = 0, 1`
  approaches `S`, but `‖u(x, y)‖ = 1`).
* `S` nonempty, as in Theorem 13.4. `K₁` nonempty is not assumed: it follows from
  approachability (the algorithm plays a point of `K₁` in round 0). -/
theorem exercise_13_3 {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁ : IsClosed K₁) (hK₁b : Bornology.IsBounded K₁) (hK₁c : Convex ℝ K₁)
    (hK₂ : IsClosed K₂) (hK₂b : Bornology.IsBounded K₂) (hK₂c : Convex ℝ K₂)
    (hS : IsClosed S) (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (hu : IsBiaffineOn K₁ K₂ u) :
    IsApproachable K₁ K₂ u S →
      ∃ O : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n),
        ∀ y ∈ K₂, O y ∈ K₁ ∧ u (O y) y ∈ S := by sorry

end OnlineConvexOpt.Approachability
