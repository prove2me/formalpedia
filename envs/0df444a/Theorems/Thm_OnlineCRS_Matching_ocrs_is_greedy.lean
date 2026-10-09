-- Prove2me | Theorems.Thm_OnlineCRS_Matching_ocrs_is_greedy
-- name    : OnlineCRS.Matching.ocrs_is_greedy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:27.260331+00:00
-- url     : https://prove2.me/theorems/2665fc0b-684d-42ab-a428-4acbfd49ab7f
-- title:
--   Proof of Theorem 2.7, p. 13 — the random-K scheme is a randomized greedy OCRS for matchings
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph. For every $x\in\mathbb R^E$ draw $K\subseteq E$ by including every edge $g$ independently with probability $q_g(x)$ (equal to $(1-e^{-x_g})/x_g$ for $x_g>0$ and to $1$ for $x_g=0$), and let $\mathcal F_K$ be the family of matchings contained in $K$. Then the law of $\mathcal F_K$ is a probability distribution on families of edge sets, each family in its support contains $\varnothing$, is down-closed and consists of matchings:
--
--   $$x\ \longmapsto\ \mathrm{Law}(\mathcal F_K)\ \text{ is a randomized greedy OCRS for the matchings of }G.$$
--
--   This is the observation that for a fixed $K$ the scheme is a deterministic greedy OCRS, so that for random $K$ it is a randomized one.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.7, p. 13, first paragraph, last sentence

import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

namespace OnlineCRS.Matching

/-- Proof of Theorem 2.7, p. 13, first paragraph: for a fixed `K` the OCRS is the deterministic greedy
OCRS with family `F_{x,K}` = the matchings inside `K`, so for the random `K` it is a randomized greedy
OCRS for the matchings of `G`. -/
theorem ocrs_is_greedy {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) :
    OnlineCRS.Matroid.IsRandGreedyOCRS (EdmondsMatching65.Polyhedron.IsMatching G) (ocrsWeight G) := by sorry

end OnlineCRS.Matching
