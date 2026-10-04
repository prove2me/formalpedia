-- Prove2me | Theorems.Thm_MinimaxRegretRL_Hoeffding_lemma3_weighted
-- name    : MinimaxRegretRL.Hoeffding.lemma3_weighted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:23:04.878993+00:00
-- url     : https://prove2.me/theorems/77d35aee-5a59-439c-94a6-bbf7f3f800cb
-- title:
--   Proof of Lemma 3 — corrected gamma-weighted surrogate recursion
-- statement:
--   In one episode $k$, start at step $h$ and assume the empirical-model event, optimistic estimates at all later steps, positive counts on the remaining visited pairs, at least two actions, and $0<\delta\le1$. Write $\widetilde\delta_{k,h}$ for estimated value minus the value of the greedy policy at the visited state. With the martingale differences $\varepsilon_{k,i}$ and $\bar\varepsilon_{k,i}$, confidence width $c_{1,k,i}$, correction $c_{4,k,i}$, and Algorithm 3 bonus $b_{k,i}$ defined in Appendix B, the proof's weighted bound is
--
--   $$\widetilde\delta_{k,h}\le\sum_{i=h}^{H}\left(1+\frac1H\right)^{i-h}\left[\varepsilon_{k,i}+2\sqrt L\,\bar\varepsilon_{k,i}+c_{1,k,i}+c_{4,k,i}+b_{k,i}\right],\qquad L=\ln(5SAT/\delta).$$
--
--   The recursion isolates the contribution of concentration, sampling noise and exploration bonuses within an episode.
--
--   **Formalization Note** The appendix's range ending at $H-1$ is aligned with the algorithm's $H$ reward steps. Its later replacement of the weights by $e$ is invalid for signed martingale differences. The typical-state threshold is $4H^2L$, required by (34)–(36), rather than B.1's $2H^2L$. The proof's $c_4$ domination needs $A\ge2$, and all displayed denominators require positive counts. The $c_1$ term uses the variance of $V^*_{i+1}$, as in (32).
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), pp. 20–21, proof of Lemma 3, Eqs. (32)–(36) and gamma-weighted display

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

namespace MinimaxRegretRL.Hoeffding

/-- Proof of Lemma 3, p. 21, the γ-weighted display. The summation extends
through the algorithm's last reward step (index `H-1` in Lean). The typical
set uses threshold `4H²L` required by (34)–(36), rather than B.1's `2H²L`.
The appendix's final replacement of γ by `e` is invalid for signed martingale
differences, so this is the proof's weighted inequality. The count-positive
condition avoids Lean's zero division, and `A≥2` makes its `c₄` dominate the
remaining terms. -/
theorem lemma3_weighted {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (hA : 2 ≤ Fintype.card A)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (ω : Outcomes S K H)
    (hE : confidenceEvent M H K δ sel init ω) (k : Fin K) (h : Fin H)
    (hpositive : ∀ i : Fin H, h.val ≤ i.val → 0 < pathN M H K δ sel init ω k i)
    (hoptimistic : ∀ j : ℕ, h.val < j → j ≤ H → ∀ y : S,
      optimalValue M H j y ≤ estimatedValue M H K δ sel init ω k j y) :
    surrogateGap M H K δ sel init ω k h.val (stateAt init ω k h.val) ≤
      ∑ i : Fin H, if h.val ≤ i.val then
        (1 + (1 : ℝ) / H) ^ (i.val - h.val) *
          (epsilon M H K δ sel init ω k i +
            2 * Real.sqrt (algorithmLog (Fintype.card S) (Fintype.card A) H K δ) *
              barEpsilon M H K δ sel init ω k i +
            pathC1 M H K δ sel init ω k i +
            pathC4 M H K δ sel init ω k i +
            pathBonus M H K δ sel init ω k i)
      else 0 := by sorry

end MinimaxRegretRL.Hoeffding
