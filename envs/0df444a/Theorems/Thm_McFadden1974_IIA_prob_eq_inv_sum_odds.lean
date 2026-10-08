-- Prove2me | Theorems.Thm_McFadden1974_IIA_prob_eq_inv_sum_odds
-- name    : McFadden1974.IIA.prob_eq_inv_sum_odds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:45.877695+00:00
-- url     : https://prove2.me/theorems/ae1f8d0a-b139-4200-990c-24db85145b0d
-- title:
--   Equation (8) — multiple-choice selection probabilities in terms of binary odds
-- statement:
--   Assume the standing conditions and Axioms 1 and 2, and write $p_{xy} = P(x\mid s,\{x,y\})$ for $x\neq y$, $p_{xx}=\tfrac12$. For every possible alternative set $B$ and $x\in B$,
--   $$P(x\mid s,B) = \frac{1}{\sum_{y\in B} p_{yx}/p_{xy}}.$$
--
--   Under Independence of Irrelevant Alternatives and positivity, the multiple choice selection probabilities are determined by the binary choice probabilities.
--
--   **Formalization Note** All binary probabilities involved are positive by Axiom 2 on the possible two-element sets, so the divisions are genuine.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 110, Equation (8) (PDF p. 6)

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace McFadden1974.IIA

/-- **Equation (8)** (p. 110, PDF p. 6): "Hence, the multiple choice selection probabilities can
be written in terms of binary odds,
(8) P(x | s, B) = 1 / Σ_{y∈B} (p_yx/p_xy)."

Formalization Note: standing assumptions `IsSelectionProb` and `PairsPossible`, and Axioms 1
and 2. Every `p_yx`, `p_xy` with `x, y ∈ B` is positive (Axiom 2 on the possible set
`{x, y}`, or `½` on the diagonal), so the divisions are genuine and the denominator is at least
`p_xx/p_xx = 1`. -/
theorem prob_eq_inv_sum_odds {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x : X) (hx : x ∈ B) :
    P s B x = 1 / ∑ y ∈ B, binProb P s y x / binProb P s x y := by sorry

end McFadden1974.IIA
