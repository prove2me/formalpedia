-- Prove2me | Theorems.Thm_OnlineRandomization_Potential_greedy_choice_exists
-- name    : OnlineRandomization.Potential.greedy_choice_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:29:02.523553+00:00
-- url     : https://prove2.me/theorems/aa3a847b-c0d6-4cde-9e53-d458e4d91a0d
-- title:
--   Proof of Theorem 3.1, p. 15 — an answer m_{n+1}(r′) obeying the potential rule exists
-- statement:
--   Let $\Phi$ be an augmented potential function for a function $\alpha$ and a randomized online algorithm $G$ (Definition 3.1), and let $H$ be a randomized online algorithm, a distribution over deterministic algorithms $H_y$. Let $r \in R^n$, $t \in R$, $r' = r t$, and let $a \in A^n$ be any answer sequence of length $n$. Then there is an answer $a' \in A$ with
--   $$
--   \mathbb E_y\big[\Phi_{n+1}(r', a a', H_y(r'))\big] \ge \mathbb E_y\big[\Phi_n(r, a, H_y(r))\big].
--   $$
--
--   Applied with $a = M(r)$, this is the paper's remark that the next answer $m_{n+1}(r')$ of the algorithm $M$ of Theorem 3.1 exists, so that the rule defining $M$ can always be followed.
--
--   **Formalization Note** The claim is stated for every answer sequence $a$ of length $n$, not only for $a = M(r)$; property 3 of Definition 3.1 holds at every configuration, so the reachability of $(r, M(r), H_y(r))$ mentioned in the paper plays no role. The expectations over $y$ are Bochner integrals; the integrands take finitely many values and are measurable because each answer of $H_y$ is a measurable function of $y$. $A$ is finite and nonempty.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 15, §3, proof of Theorem 3.1, first two paragraphs

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

open MeasureTheory

theorem greedy_choice_exists {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω)
    (r : List R) (x : R) (a : List A) (ha : a.length = r.length) :
    ∃ a' : A, (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ := by sorry

end OnlineRandomization.Potential
