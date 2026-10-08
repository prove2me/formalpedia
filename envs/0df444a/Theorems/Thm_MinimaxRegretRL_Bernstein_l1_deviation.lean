-- Prove2me | Theorems.Thm_MinimaxRegretRL_Bernstein_l1_deviation
-- name    : MinimaxRegretRL.Bernstein.l1_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:45:31.015991+00:00
-- url     : https://prove2.me/theorems/2d7ea7f3-5ff3-4aae-98fa-edaebb42b6a8
-- title:
--   Proof of Lemma 1, Eq. (12) — empirical-kernel L1 deviation
-- statement:
--   Fix a state-action pair $(x,a)$ and let $T=KH$. For $\delta>0$, the probability that at some episode start with $N_k(x,a)>0$ the empirical transition row violates
--
--   $$\sum_y|\widehat P_k(y\mid x,a)-P(y\mid x,a)|\le\sqrt{\frac{2S\ln(2T/\delta)}{N_k(x,a)}}$$
--
--   is at most $\delta$. This supplies a whole-row empirical transition bound for the UCBVI-BF analysis.
--
--   **Formalization Note** The probability is simultaneous over episode starts, rather than a bound for a fixed sample size.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 17, proof of Lemma 1, Eq. (12)

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Process

open scoped Classical

namespace MinimaxRegretRL.Bernstein

/-- Proof of Lemma 1, Eq. (12), p. 17: the empirical row's L1 error,
uniform over episode starts with a positive state-action count. -/
theorem l1_deviation {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H K : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (sel : (A → ℝ) → A)
    (hsel : ∀ f : A → ℝ, ∀ a, f a ≤ f (sel f))
    (init : InitialRule S H) (x : S) (a : A) :
    probEvent M δ K H sel init (fun ω =>
      ∃ k : Fin K,
        let st := runState M δ K H sel init ω k.val
        0 < countSA st x a ∧
        (∑ y : S, abs (empiricalP st x a y - M.P x a y)) >
          Real.sqrt (2 * (Fintype.card S : ℝ) *
            Real.log (2 * (K * H : ℝ) / δ) / (countSA st x a : ℝ))) ≤ δ := by sorry

end MinimaxRegretRL.Bernstein
