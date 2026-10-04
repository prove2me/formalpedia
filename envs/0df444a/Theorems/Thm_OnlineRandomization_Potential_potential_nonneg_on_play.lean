-- Prove2me | Theorems.Thm_OnlineRandomization_Potential_potential_nonneg_on_play
-- name    : OnlineRandomization.Potential.potential_nonneg_on_play
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:28:55.817152+00:00
-- url     : https://prove2.me/theorems/383066d7-cc18-4621-89e1-b1a861e4fdce
-- title:
--   Proof of Lemma 3.1, p. 15 — the expected augmented potential at the end of a play is nonnegative
-- statement:
--   Let $\Phi$ be an augmented potential function for a function $\alpha$ and a randomized online algorithm $G$ (Definition 3.1), and let $S$ be an adaptive on-line adversary. Let $(r, a, b)$ be the random final configuration of the play of $G$ against $S$, of random length $n$. Then
--   $$
--   \mathbb E\big[\Phi_n(r, a, b)\big] \ge 0 .
--   $$
--
--   This is the first step of the "if" direction of Lemma 3.1: combined with property 2 of Definition 3.1 it bounds the algorithm's expected cost by the adversary's.
--
--   **Formalization Note** $G$ is given in behavioural form (next-answer distributions $g_{n+1}$) and the expectation is the finite sum over the law of the final configuration; see the definitions of the mission. Costs are real-valued (the paper allows $+\infty$). No hypothesis on $\alpha$ is needed or assumed.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 14-15, §3, proof of Lemma 3.1 ('if' part), first sentence

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

theorem potential_nonneg_on_play {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ)
    (S : OnlineAdv R A) :
    0 ≤ pexp (behPlay g S) (fun z => Φ z.1 z.2.1 z.2.2) := by sorry

end OnlineRandomization.Potential
