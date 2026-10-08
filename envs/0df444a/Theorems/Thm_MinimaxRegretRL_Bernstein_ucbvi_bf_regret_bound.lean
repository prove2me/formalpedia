-- Prove2me | Theorems.Thm_MinimaxRegretRL_Bernstein_ucbvi_bf_regret_bound
-- name    : MinimaxRegretRL.Bernstein.ucbvi_bf_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:45:36.853987+00:00
-- url     : https://prove2.me/theorems/21490c43-d7db-4155-ab56-fdbfc08927c2
-- title:
--   Theorem 2 — high-probability regret bound for UCBVI-BF
-- statement:
--   Consider any finite MDP with a stationary transition kernel and known deterministic rewards in $[0,1]$, any horizon $H\ge1$, $K$ episodes, and $\delta>0$. The environment may choose each episode's initial state from completed episodes, and ties among maximizing actions may be resolved by any maximizing selection rule. Run UCBVI-BF with Algorithm 4's bonus at $L_{\rm alg}=\ln(5SAT/\delta)$, where $T=KH$. With $L=\ln(5HSAT/\delta)$, the regret obeys
--
--   $$\Pr\!\left\{\operatorname{Regret}(K)>30HL\sqrt{SAK}+2500H^2S^2AL^2+4H^{3/2}\sqrt{KL}\right\}\le\delta.$$
--
--   The bound gives the paper's explicit high-probability guarantee for its variance-sensitive value-iteration algorithm.
--
--   **Formalization Note** The bad-event form means probability at least $1-\delta$. The theorem states the paper's constants verbatim. Its appendix's Lemma 13 to Lemma 14 calculation does not reproduce the second-order $2500H^2S^2AL^2$ constant; that proof gap is not encoded as an extra assumption.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 5, Theorem 2; pp. 28–29, C.2 and Lemmas 13–14

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Process

open scoped Classical

namespace MinimaxRegretRL.Bernstein

/-- Theorem 2, p. 5, with the exact printed constants. The bonus uses
`algorithmLog = log(5SAT/δ)` while this bound uses `log(5HSAT/δ)`. -/
theorem ucbvi_bf_regret_bound {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H K : ℕ) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (sel : (A → ℝ) → A)
    (hsel : ∀ f : A → ℝ, ∀ a, f a ≤ f (sel f))
    (init : InitialRule S H) :
    let L := Real.log (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H) / δ)
    probEvent M δ K H sel init (fun ω =>
      30 * H * L * Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A * L ^ 2 +
        4 * H * Real.sqrt H * Real.sqrt (K * L) <
          regret M δ K H sel init ω) ≤ δ := by sorry

end MinimaxRegretRL.Bernstein
