-- Prove2me | Theorems.Thm_McFadden1974_IIA_binary_odds_eq
-- name    : McFadden1974.IIA.binary_odds_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:31.52471+00:00
-- url     : https://prove2.me/theorems/452171cb-055f-4279-aba0-05a4baeff2b8
-- title:
--   Equation (5) — under Axiom 1, binary odds equal the odds within any possible set
-- statement:
--   Let selection probabilities $P(\cdot\mid s,B)$ be probability vectors on every possible alternative set $B$, let every two-element subset of a possible set be possible, and let Axiom 1 (Independence of Irrelevant Alternatives) hold. Let $B$ be a possible alternative set, $s$ an attribute vector, and $x \neq y$ two members of $B$ with $P(x\mid s,B) > 0$. Then $P(x\mid s,\{x,y\}) > 0$ and
--   $$\frac{P(y\mid s,\{x,y\})}{P(x\mid s,\{x,y\})} = \frac{P(y\mid s,B)}{P(x\mid s,B)}.$$
--
--   The odds of $y$ being chosen over $x$ in a multiple choice situation $B$ where both are available equal the odds of a binary choice of $y$ over $x$.
--
--   **Formalization Note** Axiom 2 is not assumed; only $P(x\mid s,B)>0$. Positivity of the binary probability uses that $P(\cdot\mid s,\{x,y\})$ sums to one. The case $x=y$ is excluded because the singleton $\{x\}$ need not be a possible set.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 109, Equation (5) (PDF p. 5)

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace McFadden1974.IIA

/-- **Equation (5)** (p. 109, PDF p. 5): "When P(x | s, B) is positive, Equation (4) implies
P(x | s, {x, y}) positive, and
(5) P(y | s, {x, y}) / P(x | s, {x, y}) = P(y | s, B) / P(x | s, B)."

Formalization Note: the selection probabilities are probability vectors on every possible set
(`IsSelectionProb`), binary subsets of possible sets are possible (`PairsPossible`), and Axiom 1
holds; Axiom 2 is **not** assumed, only `0 < P(x | s, B)` for the one `x`. The normalisation
on the binary set is what makes `P(x | s, {x, y})` positive: without it the zero function
satisfies (4). The hypothesis `x ≠ y` excludes the degenerate case `{x, y} = {x}`: a singleton
need not be a possible set, so `P(x | s, {x})` is unconstrained there (the paper sets
`p_xx = ½` by definition instead, p. 109). -/
theorem binary_odds_eq {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss) (hA1 : Axiom1 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y : X) (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y)
    (hpos : 0 < P s B x) :
    0 < P s {x, y} x ∧ P s {x, y} y / P s {x, y} x = P s B y / P s B x := by sorry

end McFadden1974.IIA
