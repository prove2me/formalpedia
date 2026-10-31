-- Prove2me | Theorems.Thm_MalleableSched_pseudoforest_orientation
-- name    : MalleableSched.pseudoforest_orientation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:53.521924+00:00
-- url     : https://prove2.me/theorems/649d6163-2337-4955-8a61-b6e7ca93a334
-- title:
--   Appendix A.3 — a pseudoforest can be oriented with every in-degree at most one
-- statement:
--   Let $G$ be a finite graph that is a **pseudoforest**: every connected component is a tree or contains at most one cycle. Then the edges of $G$ can be oriented so that every vertex has in-degree at most one.
--
--   Applied to the support graph of an extreme point of (LP1), this gives Lemma 6, the orientation along which the proof of Theorem 1 rounds.
--
--   Differences from the source:
--   - reading: any pseudoforest → any finite simple graph (SimpleGraph on a Fintype) that is a pseudoforest; reason: the paper's graphs are simple bipartite support graphs and it defines pseudoforests only through their components' cycles
--   - encoding: every component a tree or with at most one cycle → IsPseudoforestGraph: every vertex set s has at most 2|s| ordered adjacent pairs inside s; reason: equivalent for finite graphs (each edge counted twice)
--   - encoding: an orientation → a relation D with D u v ↔ ¬ D v u for adjacent u, v; reason: each edge gets exactly one direction
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Appendix A.3, p.27

import Mathlib
import Definitions.Def_MalleableSched_Pseudoforest

namespace MalleableSched

/-- **A pseudoforest has an orientation with every in-degree at most one.**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Appendix A.3, p.27: "Hence, the edges of G (and of any pseudoforest) can be oriented in a
way that each node has an in-degree of at most one."

**Formalization Note.** Stated for every finite simple graph that is a pseudoforest (counting form
`IsPseudoforestGraph`: every vertex set `s` spans at most `|s|` edges), as in the parenthetical
"any pseudoforest"; the paper's `G` is the bipartite support graph, a special case. -/
theorem pseudoforest_orientation {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsPseudoforestGraph G) :
    ∃ D : V → V → Prop, IsOrientationInDegLeOne G D := by sorry

end MalleableSched
