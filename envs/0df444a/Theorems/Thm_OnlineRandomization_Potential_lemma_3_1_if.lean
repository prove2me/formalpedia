-- Prove2me | Theorems.Thm_OnlineRandomization_Potential_lemma_3_1_if
-- name    : OnlineRandomization.Potential.lemma_3_1_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:28:54.490983+00:00
-- url     : https://prove2.me/theorems/b0aba1db-aaad-4159-b9c2-c98576261578
-- title:
--   Lemma 3.1 (“if” direction), p. 14 — an augmented potential function makes G α-competitive against adaptive on-line adversaries
-- statement:
--   Let $\alpha : \mathbb R \to \mathbb R$ be linear, $\alpha(x) = c x + d$, and let $G$ be a randomized online algorithm. If there exists an augmented potential function $\Phi$ for $\alpha$ and $G$ (Definition 3.1), then $G$ is $\alpha$-competitive against any adaptive on-line adversary: for every adaptive on-line adversary $S$,
--   $$
--   \mathbb E\big[c_G(S)\big] \le \mathbb E\big[\alpha(c_S(G))\big],
--   $$
--   where $c_G(S) = f_n(r, a)$ and $c_S(G) = f_n(r, b)$ at the final configuration $(r, a, b)$ of the play of $G$ against $S$.
--
--   Lemma 3.1 of the paper is an equivalence; this item is its "if" direction, the one the paper proves. It shows that an augmented potential function is a certificate of competitiveness against the strongest on-line adversary.
--
--   **Formalization Note** $G$ is given in behavioural form (next-answer distributions), the play law and expectations are those of the mission's definitions, and $\alpha$ stays inside the expectation as on p. 9 of the paper. Costs are real-valued (the paper allows $+\infty$). Linearity of $\alpha$ is the paper's standing convention ("In this paper α and β will mean linear functions", p. 7); it is kept as a hypothesis although the argument with $\alpha$ inside the expectation does not use it. The "only if" direction is not stated: the paper gives it only as an informal sketch.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 14, Lemma 3.1 ('if' direction; proof pp. 14-15)

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

theorem lemma_3_1_if {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (hα : IsLinear α) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) :
    IsCompetitiveOnlineBeh F α g := by sorry

end OnlineRandomization.Potential
