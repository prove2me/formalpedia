-- Prove2me | Theorems.Thm_MinimaxRegretRL_Bernstein_count_deviation
-- name    : MinimaxRegretRL.Bernstein.count_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:45:13.322315+00:00
-- url     : https://prove2.me/theorems/645b8999-f045-4eed-bf2f-8bcf14efe3ec
-- title:
--   Proof of Lemma 1 — transition-count deviation before Eq. (11)
-- statement:
--   Fix states $x,y$ and an action $a$, and let $T=KH$. For $\delta>0$, with probability at least $1-\delta$, every episode start with $N_k(x,a)>0$ satisfies
--
--   $$|N_k(x,a,y)-N_k(x,a)P(y\mid x,a)|\le\sqrt{2N_k(x,a)P(y\mid x,a)(1-P(y\mid x,a))\ln(2T/\delta)}+\frac{2\ln(2T/\delta)}{3}.$$
--
--   This controls an individual empirical transition count at the random number of visits observed so far.
--
--   **Formalization Note** This is the display before Eq. (11). The printed Eq. (11) drops the factor $2$ under the square root after division by $N_k$; that later equation is not asserted here.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 17, proof of Lemma 1, display before Eq. (11)

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Process

open scoped Classical

namespace MinimaxRegretRL.Bernstein

/-- Proof of Lemma 1, display preceding (11), p. 17. The variance of the
indicator of `y` is `P(y|x,a)(1-P(y|x,a))`. -/
theorem count_deviation {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H K : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (sel : (A → ℝ) → A)
    (hsel : ∀ f : A → ℝ, ∀ a, f a ≤ f (sel f))
    (init : InitialRule S H) (x y : S) (a : A) :
    probEvent M δ K H sel init (fun ω =>
      ∃ k : Fin K,
        let st := runState M δ K H sel init ω k.val
        0 < countSA st x a ∧
        abs ((st.triples x a y : ℝ) - (countSA st x a : ℝ) * M.P x a y) >
          Real.sqrt (2 * (countSA st x a : ℝ) * M.P x a y * (1 - M.P x a y) *
            Real.log (2 * (K * H : ℝ) / δ)) +
          2 * Real.log (2 * (K * H : ℝ) / δ) / 3) ≤ δ := by sorry

end MinimaxRegretRL.Bernstein
