-- Prove2me | Theorems.Thm_MinimaxRegretRL_Bernstein_bernstein_random_count
-- name    : MinimaxRegretRL.Bernstein.bernstein_random_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:44:48.565269+00:00
-- url     : https://prove2.me/theorems/9adb59bf-4b95-4cfe-ad80-e6f7818ae2d7
-- title:
--   Proof of Lemma 1, Eq. (9) — Bernstein bound at random counts
-- statement:
--   Fix a step $h$, state $x$, and action $a$ in the UCBVI-BF process, and let $T=KH$. For $\delta>0$, the probability that some episode starts with $N_k(x,a)>0$ and violates
--
--   $$\left|[(P-\widehat P_k)V_h^*](x,a)\right|\le\sqrt{\frac{2\mathbb V_h^*(x,a)\ln(2T/\delta)}{N_k(x,a)}}+\frac{2H\ln(2T/\delta)}{3N_k(x,a)}$$
--
--   is at most $\delta$. Here $\mathbb V_h^*(x,a)$ is the variance of $V_h^*(Y)$ for $Y\sim P(\cdot\mid x,a)$. This is the concentration input for controlling the empirical transition model.
--
--   **Formalization Note** The probability is simultaneous over episode starts, for a fixed $h,x,a$. The source indexes steps from one and Lean from zero.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 17, proof of Lemma 1, Eq. (9)

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Process

open scoped Classical

namespace MinimaxRegretRL.Bernstein

/-- Proof of Lemma 1, Eq. (9), p. 17. The event ranges over all episode starts;
only positive counts use the empirical row. -/
theorem bernstein_random_count {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H K : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (sel : (A → ℝ) → A)
    (hsel : ∀ f : A → ℝ, ∀ a, f a ≤ f (sel f))
    (init : InitialRule S H) (h : Fin H) (x : S) (a : A) :
    probEvent M δ K H sel init (fun ω =>
      ∃ k : Fin K,
        let st := runState M δ K H sel init ω k.val
        0 < countSA st x a ∧
        abs (transitionExp M x a (optimalValue M H h.val) -
          empiricalExp st x a (optimalValue M H h.val)) >
          Real.sqrt (2 * transitionVar M x a (optimalValue M H h.val) *
            Real.log (2 * (K * H : ℝ) / δ) / (countSA st x a : ℝ)) +
          2 * H * Real.log (2 * (K * H : ℝ) / δ) / (3 * (countSA st x a : ℝ))) ≤ δ := by sorry

end MinimaxRegretRL.Bernstein
