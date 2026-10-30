-- Prove2me | Theorems.Thm_OnlineConvexOpt_Approachability_theorem_13_4
-- name    : OnlineConvexOpt.Approachability.theorem_13_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:14.720992+00:00
-- url     : https://prove2.me/theorems/7087ef81-eb7c-4e8c-bde0-40d61be7d547
-- title:
--   Theorem 13.4: Blackwell's approachability theorem for generalized vector games (corrected: payoff u bi-affine)
-- statement:
--   Let $\mathcal K_1\subseteq\mathbb R^n$ be nonempty, bounded, closed and convex, let $\mathcal K_2\subseteq\mathbb R^m$ be bounded, closed and convex, and let the reward vector $u(x,y)\in\mathbb R^d$ be bi-affine on $\mathcal K_1\times\mathcal K_2$. Let $S\subseteq\mathbb R^d$ be nonempty, closed, bounded and convex. Then the following are equivalent:
--
--   1. Blackwell's condition:
--   $$
--   \forall y\in\mathcal K_2\ \ \exists x\in\mathcal K_1:\quad u(x,y)\in S ;
--   $$
--   2. $S$ is approachable: some algorithm $\mathcal K_1\ni x_t\leftarrow\mathcal A(y_0,\dots,y_{t-1})$ satisfies, for every sequence $y_0,y_1,\dots\in\mathcal K_2$,
--   $$
--   \mathrm{Dist}\Bigl(\frac1T\sum_{t=0}^{T-1}u(x_t,y_t),\,S\Bigr)\to 0\qquad(T\to\infty);
--   $$
--   3. $S$ is uniformly approachable: the convergence in 2 holds uniformly over all sequences in $\mathcal K_2$.
--
--   Blackwell's theorem characterizes, by a one-shot condition, the target sets that a player can force the long-run average of a vector payoff into, against an arbitrary opponent. Its proof through online convex optimization shows that approachability and no-regret learning are algorithmically equivalent.
--
--   **Formalization Note** The theorem is the conjunction of two equivalences, condition ↔ `IsApproachable` and condition ↔ `IsUniformlyApproachable`. Algorithms are deterministic functions of the history (`IsApproachabilityAlg`), rounds are numbered from $0$, and $\mathrm{Dist}$ is `Metric.infDist`.
--
--   Differences from the source:
--   - correction: Definition 13.2 puts no condition on the payoff u → hypothesis IsBiaffineOn K₁ K₂ u (u preserves convex combinations in each argument on K₁ × K₂); reason: the printed statement is false for arbitrary continuous u: with K₁ = K₂ = [0,1], S = {0}, u(x,y) = (x − y)², the condition holds but the adversary y_t = 1 if x_t < 1/2, else 0, keeps every payoff ≥ 1/4; with K₁ = K₂ = [0,1], S = {(0,0)}, u(x,y) = (cos πx, sin πx), the condition fails but alternating x_t = 0, 1 gives averages within 1/T of S. Bi-affinity is the hypothesis of the chapter's source (Abernethy–Bartlett–Hazan 2011) and holds for the mixed extension of Definition 13.1
--   - generalization: "approachable" (Definition 13.3: for any sequence, Dist → 0), one reading → both readings: condition ↔ IsApproachable (per sequence) and condition ↔ IsUniformlyApproachable (uniform over sequences); reason: the definition is ambiguous between the two; the conjunction states the theorem for each, and each conjunct is the book's statement under that reading
--   - encoding: S closed, bounded and convex, with Dist(w,S) = min over S → additionally S.Nonempty; reason: a min over the empty set is undefined; Lean's Metric.infDist w ∅ = 0 would make ∅ approachable
--   - encoding: K₁ a decision set → additionally K₁.Nonempty; reason: with no decision the algorithm (and the best response) is undefined; with K₁ = K₂ = ∅ the condition holds vacuously while no algorithm exists
--   - encoding: an algorithm x_t ← A(y_1, …, y_{t−1}), rounds t = 1, …, T, Dist the min over S → a deterministic A t (y₀, …, y_{t−1}) ∈ K₁ on K₂-histories, rounds 0-indexed, average (1/T)∑_{t<T}, Dist = Metric.infDist; reason: the same objects; infDist equals the printed min for nonempty closed S
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Theorem 13.4, p. 209 (PDF p. 231); Definitions 13.2–13.3, pp. 208–209 (PDF pp. 230–231)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsBiaffineOn
import Definitions.Def_OnlineConvexOpt_Approachability_IsApproachable
import Definitions.Def_OnlineConvexOpt_Approachability_IsUniformlyApproachable

namespace OnlineConvexOpt.Approachability

/-- **Theorem 13.4 (Blackwell's Approachability Theorem), corrected: payoff `u` bi-affine.**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Theorem 13.4,
p. 209: "For any vector game K1, K2, {u(·,·)}, the closed, bounded and convex set S ⊆ ℝ^d is
approachable if and only if the following condition holds: ∀y ∈ K2 , ∃x ∈ K1 , s.t.
u(x, y) ∈ S." Vector games are Definition 13.2 (p. 208): "two bounded convex and closed decision
sets K1, K2"; approachability is Definition 13.3 (p. 209).

Let `K₁ ⊆ ℝ^n` (nonempty) and `K₂ ⊆ ℝ^m` be bounded, closed and convex, let `u` be bi-affine on
`K₁ × K₂`, and let `S ⊆ ℝ^d` be nonempty, closed, bounded and convex. Then Blackwell's condition
`∀ y ∈ K₂, ∃ x ∈ K₁, u(x, y) ∈ S` holds iff `S` is approachable, and also iff `S` is uniformly
approachable.

**Formalization Note.**
* Correction: the theorem is false as printed for an arbitrary payoff `u`, since Definition 13.2
  puts no condition on `u`. Sufficiency fails for `K₁ = K₂ = [0,1]`, `S = {0}`,
  `u(x, y) = (x − y)²`: the condition holds (`x = y`), but against `y_t = 1` if `x_t < 1/2` and
  `y_t = 0` otherwise every payoff is `≥ 1/4`. Necessity fails for `K₁ = K₂ = [0,1]`,
  `S = {(0,0)}`, `u(x, y) = (cos πx, sin πx)`: alternating `x_t = 0, 1` gives average payoffs
  within `1/T` of `S`, but `‖u(x, y)‖ = 1`. Both payoffs are continuous. The added hypothesis
  `IsBiaffineOn K₁ K₂ u` is that of the chapter's source (Abernethy, Bartlett and Hazan 2011)
  and covers the mixed extension of Definition 13.1.
* Reading R1: "for any sequence … Dist(…) → 0" is read both per sequence (`IsApproachable`) and
  uniformly over sequences (`IsUniformlyApproachable`); the theorem is stated for both.
* `S` and `K₁` nonempty: `Dist` is a minimum over `S` (and `Metric.infDist w ∅ = 0` would make
  `∅` approachable); a decision set with no decision leaves the algorithm undefined (with
  `K₁ = K₂ = ∅` the condition holds vacuously but no algorithm exists). `K₂ = ∅` is allowed.
* Reading R2: algorithms are deterministic functions of the history, rounds 0-indexed
  (`IsApproachabilityAlg`, `avgPayoff`). `Dist` is `Metric.infDist`. -/
theorem theorem_13_4 {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁ : IsClosed K₁) (hK₁b : Bornology.IsBounded K₁) (hK₁c : Convex ℝ K₁)
    (hK₁ne : K₁.Nonempty)
    (hK₂ : IsClosed K₂) (hK₂b : Bornology.IsBounded K₂) (hK₂c : Convex ℝ K₂)
    (hS : IsClosed S) (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (hu : IsBiaffineOn K₁ K₂ u) :
    ((∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) ↔ IsApproachable K₁ K₂ u S) ∧
      ((∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) ↔ IsUniformlyApproachable K₁ K₂ u S) := by sorry

end OnlineConvexOpt.Approachability
