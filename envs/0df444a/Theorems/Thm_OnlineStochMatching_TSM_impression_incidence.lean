-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_impression_incidence
-- name    : OnlineStochMatching.TSM.impression_incidence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:34:23.632807+00:00
-- url     : https://prove2.me/theorems/37ff5835-d50e-46c9-a4de-a33aaa2598e7
-- title:
--   Section 4.2.1, p. 7 — every impression type has no coloured edge, one blue edge, or one blue and one red edge
-- statement:
--   Let $G = (A, I, E)$ be a finite bipartite graph, $E_f$ the edge set of an integral maximum flow of the boosted flow graph, and blue/red a TSM colouring of $E_f$. Then every impression type $i \in I$ is incident to either
--   1. no coloured edge,
--   2. exactly one blue edge and no red edge, or
--   3. exactly one blue edge and exactly one red edge.
--
--   This is what makes the two suggested matchings algorithm well defined: "the advertiser along $i$'s blue edge" and "the advertiser along $i$'s red edge" are unique when they exist, and a type with no blue edge has no red edge either.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 7, Section 4.2.1 (note after the colouring rules)

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring

namespace OnlineStochMatching.TSM

/-- **The note of §4.2.1** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching:
Beating 1-1/e*, arXiv:0905.4100v1, p. 7): for a maximum flow edge set `E_f` and a TSM colouring
`(blue, red)` of it, every impression type `i` is incident to either no coloured edge, exactly one
blue edge (and no red edge), or exactly one blue and exactly one red edge. In particular "the ad
along `i`'s blue edge" and "the ad along `i`'s red edge" are well defined. -/
theorem impression_incidence {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F blue red : Finset (A × I)) (hF : IsMaxFlowSet E F) (hcol : IsTSMColoring F blue red)
    (i : I) :
    (degI blue i = 0 ∧ degI red i = 0) ∨ (degI blue i = 1 ∧ degI red i = 0) ∨
      (degI blue i = 1 ∧ degI red i = 1) := by sorry

end OnlineStochMatching.TSM
