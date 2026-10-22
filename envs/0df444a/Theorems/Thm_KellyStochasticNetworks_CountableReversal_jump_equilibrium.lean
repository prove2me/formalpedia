-- Prove2me | Theorems.Thm_KellyStochasticNetworks_CountableReversal_jump_equilibrium
-- name    : KellyStochasticNetworks.CountableReversal.jump_equilibrium
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:50.469373+00:00
-- url     : https://prove2.me/theorems/d07046db-d718-4f7b-ac1f-c279d9ab523b
-- title:
--   Exercise 1.2 — equilibrium distribution of the jump chain
-- statement:
--   Let $S$ be a nonempty countable state space and $q(j,k)$ nonnegative jump rates with $q(j,j)=0$ and positive finite exit rates $q(j)=\sum_kq(j,k)$. Assume irreducibility. Let $\pi$ be strictly positive, sum to one, and satisfy the equilibrium equations with convergent incoming sums. Suppose
--   $$
--   G=\sum_j\pi(j)q(j)=\sum_j\sum_k\pi(j)q(j,k)<\infty.
--   $$
--   Then $G>0$, the jump probabilities $p(j,k)=q(j,k)/q(j)$ form a stochastic matrix, and
--   $$
--   \pi^J(j)=G^{-1}\pi(j)q(j),\qquad
--   \sum_j\pi^J(j)=1,\qquad
--   \pi^J(j)=\sum_k\pi^J(k)p(k,j).
--   $$
--   Every $\pi^J(j)$ is positive. This identifies the equilibrium distribution at successive jumps, as distinct from the distribution at a fixed time.
--
--   **Formalization Note** Equilibrium of the jump chain is expressed by normalization and its invariant-vector equations for the kernel fixed by the book. The result is stated on the rates and equilibrium distribution supplied by the process; no arbitrary jump kernel is introduced. `Summable` expresses finiteness of $G$, while `HasSum` expresses normalization and convergent balance. Positivity of $G$ is a conclusion, not an extra hypothesis.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 16 (PDF p. 24), Exercise 1.2 and Eq. (1.3); standing assumptions printed pp. 13–15 (PDF pp. 21–23); https://doi.org/10.1017/CBO9781139565363

import Mathlib

open scoped BigOperators

namespace KellyStochasticNetworks.CountableReversal

theorem jump_equilibrium {S : Type*} [Countable S] [Nonempty S]
    (q : S → S → ℝ) (π : S → ℝ)
    (hq : ∀ j k, 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hqsum : ∀ j, Summable (q j)) (hqpos : ∀ j, 0 < ∑' k, q j k)
    (hirr : ∀ j k, Relation.ReflTransGen (fun a b => 0 < q a b) j k)
    (hπpos : ∀ j, 0 < π j) (hπsum : HasSum π 1)
    (hbalance : ∀ j, HasSum (fun k => π k * q k j) (π j * ∑' k, q j k))
    (hG : Summable (fun j => π j * ∑' k, q j k)) :
    let G := ∑' j, π j * ∑' k, q j k
    let πJ := fun j => G⁻¹ * π j * (∑' k, q j k)
    let p := fun j k => q j k / (∑' l, q j l)
    0 < G ∧ (∀ j, 0 < πJ j) ∧ HasSum πJ 1 ∧
      (∀ j k, 0 ≤ p j k) ∧ (∀ j, HasSum (p j) 1) ∧
      (∀ j, HasSum (fun k => πJ k * p k j) (πJ j)) := by sorry

end KellyStochasticNetworks.CountableReversal
