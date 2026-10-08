-- Prove2me | Theorems.Thm_McFadden1974_IIA_prob_eq_odds_mul
-- name    : McFadden1974.IIA.prob_eq_odds_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:44.847984+00:00
-- url     : https://prove2.me/theorems/25a83e48-b109-4b8b-a60b-199295fa6fb2
-- title:
--   Equations (6)–(7) — selection probabilities in a possible set are proportional to binary odds
-- statement:
--   Assume the standing conditions (each $P(\cdot\mid s,B)$ is a probability vector on a possible $B$; two-element subsets of possible sets are possible) and Axioms 1 and 2. Write $p_{xy} = P(x\mid s,\{x,y\})$ for $x\neq y$ and $p_{xx}=\tfrac12$. For a possible alternative set $B$ and $x \in B$:
--   $$P(y\mid s,B) = \frac{p_{yx}}{p_{xy}}\,P(x\mid s,B)\quad\text{for every } y\in B, \tag{6}$$
--   $$1 = \Big(\sum_{y\in B}\frac{p_{yx}}{p_{xy}}\Big)\,P(x\mid s,B). \tag{7}$$
--
--   These identities express every selection probability in $B$ through one of them and the binary odds.
--
--   **Formalization Note** The middle term $\sum_{y\in B}P(y\mid s,B)=1$ of the paper's (7) is the standing probability-vector assumption; the theorem asserts the outer equality.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 109, Equations (6)-(7) (PDF p. 5)

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace McFadden1974.IIA

/-- **Equations (6)–(7)** (p. 109, PDF p. 5): "Consider a choice set B containing alternatives
x, y, z, and let p_xy = P(x | s, {x, y}). Define p_xx = ½. From Equation (4),
(6) P(y | s, B) = (p_yx / p_xy) P(x | s, B)
and
(7) 1 = Σ_{y∈B} P(y | s, B) = (Σ_{y∈B} p_yx / p_xy) P(x | s, B)."

Formalization Note: standing assumptions `IsSelectionProb` and `PairsPossible`, and Axioms 1
and 2. `binProb P s x y` is `p_xy` (with `p_xx = ½`). The middle term `Σ_{y∈B} P(y | s, B) = 1`
of (7) is the standing assumption itself; the theorem asserts (6) for every `y ∈ B` and the
outer equality of (7). -/
theorem prob_eq_odds_mul {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x : X) (hx : x ∈ B) :
    (∀ y ∈ B, P s B y = (binProb P s y x / binProb P s x y) * P s B x) ∧
      1 = (∑ y ∈ B, binProb P s y x / binProb P s x y) * P s B x := by sorry

end McFadden1974.IIA
