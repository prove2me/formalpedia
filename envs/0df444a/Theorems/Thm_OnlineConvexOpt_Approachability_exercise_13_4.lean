-- Prove2me | Theorems.Thm_OnlineConvexOpt_Approachability_exercise_13_4
-- name    : OnlineConvexOpt.Approachability.exercise_13_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:04.832054+00:00
-- url     : https://prove2.me/theorems/24921d26-bb6c-4071-a08e-8d05a51232b4
-- title:
--   Exercise 13.4: Blackwell's condition is sufficient, at rate $O(1/\sqrt T)$ (corrected: payoff u bi-affine)
-- statement:
--   Let $\mathcal K_1\subseteq\mathbb R^n$ be nonempty, bounded, closed and convex, let $\mathcal K_2\subseteq\mathbb R^m$ be bounded, closed and convex, let $u$ be bi-affine on $\mathcal K_1\times\mathcal K_2$, and let $S\subseteq\mathbb R^d$ be nonempty, bounded, closed and convex. Suppose Blackwell's condition holds:
--
--   $$
--   \forall y\in\mathcal K_2\ \ \exists x\in\mathcal K_1:\quad u(x,y)\in S .
--   $$
--
--   Then there are an admissible algorithm $\mathcal A$ for the row player (playing in $\mathcal K_1$ whenever the past column plays lie in $\mathcal K_2$) and a constant $C$ such that for every sequence $y_0,y_1,\dots\in\mathcal K_2$ and every $T\ge 1$,
--
--   $$
--   \mathrm{Dist}\Bigl(\frac1T\sum_{t=0}^{T-1}u(x_t,y_t),\,S\Bigr)\le\frac{C}{\sqrt T},\qquad x_t=\mathcal A_t(y_0,\dots,y_{t-1}).
--   $$
--
--   In particular $S$ is approachable, in the per-sequence and in the uniform sense. This is the sufficiency half of Blackwell's theorem, obtained from the first reduction of the chapter (Theorem 13.7) and an OCO algorithm such as online gradient descent (Theorem 3.1).
--
--   **Formalization Note** $C$ is chosen after the algorithm and before the sequence. The average payoff is `avgPayoff` and $\mathrm{Dist}$ is `Metric.infDist`.
--
--   Differences from the source:
--   - correction: Definition 13.2 puts no condition on the payoff u → hypothesis IsBiaffineOn K₁ K₂ u (u preserves convex combinations in each argument on K₁ × K₂); reason: the printed statement is false for arbitrary continuous u: with K₁ = K₂ = [0,1], S = {0}, u(x,y) = (x − y)², the condition holds but the adversary y_t = 1 if x_t < 1/2, else 0, keeps every payoff ≥ 1/4; with K₁ = K₂ = [0,1], S = {(0,0)}, u(x,y) = (cos πx, sin πx), the condition fails but alternating x_t = 0, 1 gives averages within 1/T of S. Bi-affinity is the hypothesis of the chapter's source (Abernethy–Bartlett–Hazan 2011) and holds for the mixed extension of Definition 13.1
--   - generalization: S is approachable → a uniform rate C/√T for every sequence in K₂ and every T ≥ 1, C independent of the sequence; reason: the rate implies both readings of approachability (C/√T → 0 uniformly)
--   - encoding: the existence of an oracle O with u(O(y), y) ∈ S for all y → ∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S; reason: equivalent by choice
--   - encoding: K₁ a decision set → additionally K₁.Nonempty; reason: with no decision the algorithm (and the best response) is undefined; with K₁ = K₂ = ∅ the condition holds vacuously while no algorithm exists
--   - encoding: S closed, bounded and convex, with Dist(w,S) = min over S → additionally S.Nonempty; reason: a min over the empty set is undefined; Lean's Metric.infDist w ∅ = 0 would make ∅ approachable
--   - encoding: an algorithm x_t ← A(y_1, …, y_{t−1}), rounds t = 1, …, T, Dist the min over S → a deterministic A t (y₀, …, y_{t−1}) ∈ K₁ on K₂-histories, rounds 0-indexed, average (1/T)∑_{t<T}, Dist = Metric.infDist; reason: the same objects; infDist equals the printed min for nonempty closed S
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Chapter 13, Exercise 4, p. 218 (PDF p. 240); with Theorem 13.7, p. 212 (PDF p. 234)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsBiaffineOn
import Definitions.Def_OnlineConvexOpt_Approachability_IsApproachabilityAlg
import Definitions.Def_OnlineConvexOpt_Approachability_avgPayoff

namespace OnlineConvexOpt.Approachability

/-- **Exercise 13.4 (sufficiency of Blackwell's condition), with an `O(1/√T)` rate.**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Chapter 13,
Exercise 4, p. 218: "Complete the proof of Blackwell’s theorem using the first reduction of this
chapter and the existence of OCO algorithms. That is, prove that for a given vector game, the
existence of an oracle as per the previous question, is sufficient for a set S ⊆ ℝ^d to be
approachable."

For bounded closed convex `K₁` (nonempty) and `K₂`, a payoff `u` bi-affine on `K₁ × K₂`, and a
nonempty bounded closed convex `S`: if every `y ∈ K₂` has a response `x ∈ K₁` with
`u(x, y) ∈ S`, then there are an algorithm `A` playing in `K₁` on `K₂`-histories and a constant
`C` such that for every sequence `y : ℕ → K₂` and every `T ≥ 1`,
`Dist(avgPayoff u A y T, S) ≤ C / √T`.

**Formalization Note.**
* Generalization: the exercise asks for approachability; the Lean conclusion is a uniform rate
  `C/√T` (the rate "borrowed from the OCO algorithms", p. 207, via Theorem 13.7 and
  Theorem 3.1). It implies both `IsApproachable` and `IsUniformlyApproachable`. `C` is chosen
  after `A` and before the sequence.
* "The existence of an oracle as per the previous question" (an `O` with `u(O(y), y) ∈ S` for
  all `y`) is written as `∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S`; the two are equivalent by choice.
  "A given vector game" is a generalized vector game of Definition 13.2 (the exercise's `∆_m`
  in Exercise 3 is the finite special case).
* Correction: `u` bi-affine on `K₁ × K₂` (`IsBiaffineOn`); without it the statement is false
  (`K₁ = K₂ = [0,1]`, `S = {0}`, `u(x, y) = (x − y)²`: the condition holds, but against
  `y_t = 1` if `x_t < 1/2` and `y_t = 0` otherwise every payoff is `≥ 1/4`).
* `K₁` and `S` nonempty, as in Theorem 13.4. Rounds are 0-indexed (`avgPayoff`). -/
theorem exercise_13_4 {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁ : IsClosed K₁) (hK₁b : Bornology.IsBounded K₁) (hK₁c : Convex ℝ K₁)
    (hK₁ne : K₁.Nonempty)
    (hK₂ : IsClosed K₂) (hK₂b : Bornology.IsBounded K₂) (hK₂c : Convex ℝ K₂)
    (hS : IsClosed S) (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (hu : IsBiaffineOn K₁ K₂ u) :
    (∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) →
      ∃ A : (t : ℕ) → (Fin t → EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n),
        IsApproachabilityAlg K₁ K₂ A ∧
          ∃ C : ℝ, ∀ y : ℕ → EuclideanSpace ℝ (Fin m), (∀ t, y t ∈ K₂) →
            ∀ T : ℕ, 1 ≤ T → Metric.infDist (avgPayoff u A y T) S ≤ C / Real.sqrt T := by sorry

end OnlineConvexOpt.Approachability
