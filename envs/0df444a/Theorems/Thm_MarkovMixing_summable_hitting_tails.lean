-- Prove2me | Theorems.Thm_MarkovMixing_summable_hitting_tails
-- name    : MarkovMixing.summable_hitting_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:01.821189+00:00
-- url     : https://prove2.me/theorems/13e33a62-6d3a-4214-b4ed-c2ab6002bc6a
-- title:
--   Lemma 1.13 -- expected hitting times of an irreducible chain are finite
-- statement:
--   For an irreducible chain and any states $x,z$, the expected first hitting time $\mathbb{E}_x(\tau_z^+)$ is finite. Formally: the tail probabilities $\mathbb{P}_x\{\tau_z^+>t\}$, expressed as finite sums of trajectory weights, form a summable family in $t$ -- their sum being the expectation by the tail-sum formula $\mathbb{E}Y=\sum_{t\ge0}\mathbb{P}\{Y>t\}$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.5.2, Lemma 1.13, p. 11

import Definitions.Def_mm_path

namespace MarkovMixing

/-- **Lemma 1.13** (LPW): for an irreducible chain, `E_x(τ⁺_z) < ∞` for all
states `x, z` — formalized as summability of the tail probabilities
`P_x{τ⁺_z > t}`, whose sum is the expectation. -/
theorem summable_hitting_tails {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P) (x z : V) :
    Summable (fun t : ℕ => avoidTailProb P x z t) := by
  sorry

end MarkovMixing
