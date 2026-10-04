-- Prove2me | Theorems.Thm_MinimaxRegretRL_Hoeffding_ucbvi_ch_regret_bound
-- name    : MinimaxRegretRL.Hoeffding.ucbvi_ch_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:23:15.215763+00:00
-- url     : https://prove2.me/theorems/77097656-815a-4dfa-971d-f12efbfb0a12
-- title:
--   Theorem 1 — high-probability regret bound for UCBVI-CH
-- statement:
--   Consider a finite episodic MDP with stationary transition probabilities, known deterministic rewards in $[0,1]$, nonempty finite state and action sets, episode length $H\ge1$, and $K$ episodes. Run UCBVI-CH with Algorithm 3's bonus and any maximizing tie-break rule. The environment may choose each episode's initial state from the preceding episodes. For every $\delta>0$, with $T=KH$ and $L=\ln(5HSAT/\delta)$,
--
--   $$\Pr\!\left(\mathrm{Regret}(K)>20H^{3/2}L\sqrt{SAK}+250H^2S^2AL^2\right)\le\delta.$$
--
--   Here regret compares each episode's greedy policy with an optimal policy at that episode's initial state. This is the paper's explicit high-probability guarantee for the Chernoff–Hoeffding variant.
--
--   **Formalization Note** Algorithm 3 uses $\ln(5SAT/\delta)$ in the bonus, while the theorem prints $\ln(5HSAT/\delta)$ in the bound. The statement retains the printed constants. The appendix does not track the constant $20$ explicitly in its final sketch.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 5, Theorem 1; p. 4, Algorithms 1–3; p. 29, C.1

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

namespace MinimaxRegretRL.Hoeffding

/-- Theorem 1, p. 5, with its printed constants. Algorithm 3 uses
`ln(5SAT/δ)` while this bound uses `ln(5HSAT/δ)`, exactly as printed. The
paper's appendix does not explicitly track the constant `20`. -/
theorem ucbvi_ch_regret_bound {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) :
    probEvent M H K δ sel init (fun ω =>
      20 * (H : ℝ) * Real.sqrt H *
          theoremLog (Fintype.card S) (Fintype.card A) H K δ *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A *
          (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 <
        regret M H K δ sel init ω) ≤ δ := by sorry

end MinimaxRegretRL.Hoeffding
