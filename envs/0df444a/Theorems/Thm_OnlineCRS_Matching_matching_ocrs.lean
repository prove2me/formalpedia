-- Prove2me | Theorems.Thm_OnlineCRS_Matching_matching_ocrs
-- name    : OnlineCRS.Matching.matching_ocrs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:16.834485+00:00
-- url     : https://prove2.me/theorems/d3990fe7-98a4-4c30-9f90-e555b577f183
-- title:
--   Theorem 2.7, p. 13 — the degree relaxation of matching has a (b, e^{−2b})-selectable randomized greedy OCRS
-- statement:
--   Let $G=(V,E)$ be a finite graph without loops, and let
--
--   $$P_G=\Big\{x\in\mathbb R^E:\ \sum_{g\in\delta(u)}x_g\le1\ \forall u\in V,\ x_g\ge0\ \forall g\in E\Big\}\subseteq[0,1]^E$$
--
--   be the degree relaxation of matching, where $\delta(u)$ is the set of edges at $u$. For every $b\in[0,1]$ there exists a randomized greedy OCRS for $P_G$, whose families consist of matchings, that is $(b,e^{-2b})$-selectable: for every $x\in bP_G$ and every edge $g\in E$,
--
--   $$\Pr\big[g\text{ is selectable for }R(x)\text{ and the random family }\mathcal F_x\big]\ \ge\ e^{-2b}.$$
--
--   Since every element is then selected with probability at least $e^{-2b}$ when active, against any arrival order, this gives a constant-factor online rounding for matchings in general graphs; as $P_G$ contains the matching polytope, the result applies to it as well.
--
--   **Formalization Note** The scheme is a probability distribution on families of edge sets, for every $x\in\mathbb R^E$, supported on down-closed families of matchings containing $\varnothing$; probabilities are finite sums of product weights. The graph is the published `EdmondsMatching65.Polyhedron.Graph` (loopless; parallel edges allowed, a harmless generalization of the paper's graph). Selectability is required for every edge, including edges with $x_g=0$.
-- source:
--   arXiv:1508.00142v2, Theorem 2.7, p. 13 (second bullet of Theorem 1.8, p. 4)

import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

namespace OnlineCRS.Matching

/-- Theorem 2.7, p. 13: the degree relaxation of matching admits a randomized greedy OCRS. -/
theorem matching_ocrs {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ w : (E → ℝ) → Finset (Finset E) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (EdmondsMatching65.Polyhedron.IsMatching G) (matchingRelax G) b
        (Real.exp (-2 * b)) w := by sorry

end OnlineCRS.Matching
