-- Prove2me | Theorems.Thm_OnlineConvexOpt_Approachability_lemma_13_6
-- name    : OnlineConvexOpt.Approachability.lemma_13_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:42:54.732862+00:00
-- url     : https://prove2.me/theorems/7163a35f-0cba-416f-8991-aeae0ec2bfa6
-- title:
--   Lemma 13.6: two equivalent forms of Blackwell's condition (corrected: payoff u bi-affine)
-- statement:
--   Let $\mathcal K_1\subseteq\mathbb R^n$ be nonempty, bounded, closed and convex, let $\mathcal K_2\subseteq\mathbb R^m$ be bounded, closed and convex, let $u$ be bi-affine on $\mathcal K_1\times\mathcal K_2$, and let $S\subseteq\mathbb R^d$ be nonempty, bounded, closed and convex. The following two conditions are equivalent:
--
--   1. there is a feasible best response:
--   $$
--   \forall y\in\mathcal K_2\ \ \exists x\in\mathcal K_1:\quad u(x,y)\in S ;
--   $$
--   2. for every $w\in\mathbb R^d$ with $\|w\|\le 1$ there is $x\in\mathcal K_1$ such that
--   $$
--   \forall y\in\mathcal K_2:\quad w^\top u(x,y)-h_S(w)\le 0 .
--   $$
--
--   Condition 2 provides the best-response oracle $\mathcal O(w)$ of (13.2), on which the reduction from online convex optimization to approachability (Algorithm 37, Theorem 13.7) is built.
--
--   **Formalization Note** $h_S$ is `supportFun`. Bi-affinity is the predicate `IsBiaffineOn`.
--
--   Differences from the source:
--   - correction: Definition 13.2 puts no condition on the payoff u → hypothesis IsBiaffineOn K₁ K₂ u (u preserves convex combinations in each argument on K₁ × K₂); reason: the printed statement is false for arbitrary continuous u: with K₁ = K₂ = [0,1], S = {0}, u(x,y) = (x − y)², the condition holds but the adversary y_t = 1 if x_t < 1/2, else 0, keeps every payoff ≥ 1/4; with K₁ = K₂ = [0,1], S = {(0,0)}, u(x,y) = (cos πx, sin πx), the condition fails but alternating x_t = 0, 1 gives averages within 1/T of S. Bi-affinity is the hypothesis of the chapter's source (Abernethy–Bartlett–Hazan 2011) and holds for the mixed extension of Definition 13.1
--   - encoding: K₁ a decision set → additionally K₁.Nonempty; reason: with no decision the algorithm (and the best response) is undefined; with K₁ = K₂ = ∅ the condition holds vacuously while no algorithm exists
--   - encoding: S closed, bounded and convex, h_S a max over S → additionally S.Nonempty; reason: a max over the empty set is undefined; Lean's supportFun returns 0 there
--   - encoding: h_S(w) = max_{x∈S} w⊤x → supportFun S w := ⨆ s : S, ⟪w, s⟫ (real iSup); reason: for nonempty compact S the iSup is attained and equals the max
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Lemma 13.6, p. 211 (PDF p. 233)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_supportFun
import Definitions.Def_OnlineConvexOpt_Approachability_IsBiaffineOn

open scoped InnerProductSpace

namespace OnlineConvexOpt.Approachability

/-- **Lemma 13.6 (two equivalent forms of Blackwell's condition), corrected: `u` bi-affine.**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Lemma 13.6,
p. 211: "For a generalized vector game K1, K2, {u}, the following to conditions are equivalent:
1. There exists a feasible best response, ∀y ∈ K2 , ∃x ∈ K1 , s.t. u(x, y) ∈ S.
2. For all w ∈ ℝ^d, ‖w‖ ≤ 1, there exists x ∈ K1 such that ∀y ∈ K2 , w⊤u(x, y) − h_S(w) ≤ 0."

For bounded closed convex `K₁ ⊆ ℝ^n` (nonempty) and `K₂ ⊆ ℝ^m`, a payoff `u` bi-affine on
`K₁ × K₂`, and a nonempty bounded closed convex `S ⊆ ℝ^d`: condition 1 holds iff condition 2
holds.

**Formalization Note.**
* Correction: the lemma is false as printed for an arbitrary payoff `u` (Definition 13.2 puts no
  condition on `u`). With `K₁ = K₂ = [0,1]`, `S = {0}`, `u(x, y) = (x − y)²`, condition 1 holds
  (`x = y`) but condition 2 fails at `w = 1`. With `K₁ = K₂ = [0,1]`, `S = {(0,0)}`,
  `u(x, y) = (cos πx, sin πx)`, condition 2 holds (one of `x ∈ {0, 1}` gives `w⊤u ≤ 0 = h_S(w)`)
  but condition 1 fails. The hypothesis `IsBiaffineOn K₁ K₂ u` is the chapter's source's
  hypothesis and what the proof's use of Sion's minimax theorem needs.
* `K₁` nonempty: a decision set with no decision; for `K₁ = K₂ = ∅` condition 1 holds vacuously
  while condition 2 fails. `S` nonempty: `Dist` and `h_S` are a min and a max over `S`.
* Closed, bounded, convex are three separate hypotheses, as printed in Definition 13.2. -/
theorem lemma_13_6 {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁ : IsClosed K₁) (hK₁b : Bornology.IsBounded K₁) (hK₁c : Convex ℝ K₁)
    (hK₁ne : K₁.Nonempty)
    (hK₂ : IsClosed K₂) (hK₂b : Bornology.IsBounded K₂) (hK₂c : Convex ℝ K₂)
    (hS : IsClosed S) (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (hu : IsBiaffineOn K₁ K₂ u) :
    (∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) ↔
      ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖ ≤ 1 →
        ∃ x ∈ K₁, ∀ y ∈ K₂, ⟪w, u x y⟫_ℝ - supportFun S w ≤ 0 := by sorry

end OnlineConvexOpt.Approachability
