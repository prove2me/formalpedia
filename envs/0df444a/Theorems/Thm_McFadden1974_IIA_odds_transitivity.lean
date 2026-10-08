-- Prove2me | Theorems.Thm_McFadden1974_IIA_odds_transitivity
-- name    : McFadden1974.IIA.odds_transitivity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:55.61799+00:00
-- url     : https://prove2.me/theorems/dde472ab-3596-48c6-b695-c8263f222138
-- title:
--   Equation (9) — the binary odds satisfy $p_{yx}/p_{xy} = (p_{yz}/p_{zy})/(p_{xz}/p_{zx})$
-- statement:
--   Assume the standing conditions and Axioms 1 and 2, and write $p_{xy} = P(x\mid s,\{x,y\})$ for $x\neq y$, $p_{xx}=\tfrac12$. For any three (not necessarily distinct) members $x,y,z$ of a possible alternative set $B$,
--   $$\frac{p_{yx}}{p_{xy}} = \frac{p_{yz}/p_{zy}}{p_{xz}/p_{zx}}.$$
--
--   The binary odds factor through any third alternative $z$; this is the condition that allows a single benchmark alternative to generate all the odds.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 110, Equation (9) (PDF p. 6)

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace McFadden1974.IIA

/-- **Equation (9)** (p. 110, PDF p. 6): "Permuting the indices x, y, z in Equation (6) and
multiplying yields the condition
(9) p_yx / p_xy = (p_yz/p_zy) / (p_xz/p_zx)."

Formalization Note: as in (6), `x, y, z` are members of one possible alternative set `B`, on
which the standing assumptions and Axioms 1 and 2 hold; they need not be distinct (with
`p_xx = ½` the identity holds on the diagonal too). This is the form footnote 3 applies with
`B ∪ {z}` in place of `B`. -/
theorem odds_transitivity {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y z : X) (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B) :
    binProb P s y x / binProb P s x y =
      (binProb P s y z / binProb P s z y) / (binProb P s x z / binProb P s z x) := by sorry

end McFadden1974.IIA
