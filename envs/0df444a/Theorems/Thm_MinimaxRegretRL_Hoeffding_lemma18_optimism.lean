-- Prove2me | Theorems.Thm_MinimaxRegretRL_Hoeffding_lemma18_optimism
-- name    : MinimaxRegretRL.Hoeffding.lemma18_optimism
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:23:15.375146+00:00
-- url     : https://prove2.me/theorems/e46e5e41-5797-48f6-94bc-a9998ed937f5
-- title:
--   Lemma 18 — optimism of UCBVI-CH
-- statement:
--   For an $H$-step UCBVI-CH run with $0<\delta\le1$, suppose the empirical-model confidence event $\mathcal E_{\widehat P}$ holds. Then in every episode, at every step and every state, the estimated value is optimistic:
--
--   $$V_{k,h}(x)\ge V_h^*(x).$$
--
--   This property compares the algorithm's estimates with the optimal value and supports the passage from surrogate regret to actual regret.
--
--   **Formalization Note** The paper states the lemma under its full event $\mathcal E$; its proof uses only $\mathcal E_{\widehat P}$. The added condition $\delta\le1$ ensures $\ln(5SAT/\delta)>1$, needed for the printed bonus to dominate $c_1$. The algorithm's terminal step $H+1$ is included with value zero; the appendix indexes the terminal step as $H$.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 28, Lemma 18 and proof

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

namespace MinimaxRegretRL.Hoeffding

/-- Lemma 18, p. 28. `E_P̂` suffices for the proof; `δ≤1` guarantees the
printed bonus dominates the confidence width. The appendix's last index
`H` is shifted to the algorithm's terminal index `H+1` (Lean index `H`). -/
theorem lemma18_optimism {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (ω : Outcomes S K H)
    (hE : confidenceEvent M H K δ sel init ω) :
    ∀ (k : Fin K) (h : ℕ) (hh : h ≤ H) (x : S),
      optimalValue M H h x ≤ estimatedValue M H K δ sel init ω k h x := by sorry

end MinimaxRegretRL.Hoeffding
