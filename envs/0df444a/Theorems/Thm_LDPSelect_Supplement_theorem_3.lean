-- Prove2me | Theorems.Thm_LDPSelect_Supplement_theorem_3
-- name    : LDPSelect.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:04:15.108712+00:00
-- url     : https://prove2.me/theorems/73121aa2-4f55-4448-b956-e7c5d6a1ec84
-- title:
--   Theorem 3 — conflict graphs and matchings: interaction is useless iff every component is complete multipartite
-- statement:
--   Fix $1<a<\infty$.
--
--   1. Let $G$ be a finite simple graph on the users whose independent sets are the feasible sets. Interaction is useless if and only if every connected component of $G$ is complete multipartite.
--   2. Equivalently, $G$ has no induced $P_4$ and no induced paw (a triangle with a pendant edge).
--   3. In particular, for edge-arrival matching on a finite graph $J$ (feasible sets are matchings, users are edges, in any enumeration), interaction is useless if and only if every connected component of the line graph of $J$ is complete multipartite.
--   4. Bipartite matching on a five-vertex tree already exhibits a strict gain: there is a tree $J$ on five vertices and an enumeration of its edges for which some bounded prior and some arrival order give $W^{\mathrm N}<W^{\mathrm I}$.
--
--   Assignment problems with conflicts thus need adaptive reporting as soon as the conflict structure contains a $P_4$ or a paw, and matching markets need it already on trees.
--
--   **Formalization Note** $P_4$ is Mathlib's `pathGraph 4`; the paw is the graph on $\{0,1,2,3\}$ with edges $12, 03, 13, 23$, as in the published `graph_structure`. An induced subgraph is an induced embedding.
--
--   Differences from the source:
--   - encoding: a finite simple graph G whose independent sets are the feasible sets → G : SimpleGraph (Fin n) on the users; feasible sets {S | G.IsIndepSet S}; reason: the users are Fin n in arrival order; every order is covered by Useless
--   - encoding: no induced P4 and no induced paw → no induced embedding ↪g of pathGraph 4 or of the paw on Fin 4; reason: the encoding of the published graph_structure (p.8)
--   - encoding: edge-arrival matching on a graph J → matchFam J e for every finite J : SimpleGraph V (V : Type) and every enumeration e : Fin m ≃ J.edgeSet; reason: the order of e is immaterial since Useless quantifies over arrival orders; stated for every e
--   - encoding: exhibits a strict gain → HasGap a (matchFam J e): a bounded probability prior and an arrival order with W^N < W^I; reason: the published form of a strict gain; the paper's instances are bounded
--   - encoding: bipartite matching on a five-vertex tree → J : SimpleGraph (Fin 5) with J.IsTree; reason: every tree is bipartite
--   - encoding: interaction is useless → the published Useless: W^I = W^N for every arrival order σ and every integrable product prior; reason: the definition of §1.1, p.1
--   - encoding: every product prior → every family of probability measures on ℝ≥0 with finite means, indexed by arrival position; reason: the standing assumption of §2: values are independent, non-negative and integrable
--   - encoding: W^I and W^N of Definition 8 → the published WI and WN (suprema in [0, ∞] over output types Z : Type and private mechanisms with behaviour-strategy acceptance kernels); reason: the published base model of this mission, whose conventions are listed with LDPSelect.theorem_1
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 3, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Supplement_Matching

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

open LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 3, p.2 (pdf p.3).

Fix `1 < a < ∞` and a finite simple graph `G` whose independent sets are the feasible sets. Interaction
is useless if and only if every connected component of `G` is complete multipartite, equivalently, `G`
has no induced `P4` and no induced paw. In particular, for edge-arrival matching on a graph `J`,
interaction is useless if and only if every component of the line graph of `J` is complete multipartite;
bipartite matching on a five-vertex tree already exhibits a strict gain.

**Formalization Note.** `G` lives on the users `Fin n`. The paw is the triangle on `1, 2, 3` with the
pendant edge `03`, and `P4` is `pathGraph 4`, as in the published `graph_structure`; an induced subgraph is
an induced embedding `↪g`. Edge-arrival matching uses `matchFam J e` for every enumeration `e` of the
edges of `J`. A strict gain is the published `HasGap` (a bounded prior and an arrival order with
`W^N < W^I`); a tree is bipartite. -/
theorem theorem_3 (a : ℝ) (ha : 1 < a) :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (Useless a {S : Finset (Fin n) | G.IsIndepSet (↑S : Set (Fin n))} ↔
        ∀ C : G.ConnectedComponent, C.toSimpleGraph.IsCompleteMultipartite) ∧
      ((∀ C : G.ConnectedComponent, C.toSimpleGraph.IsCompleteMultipartite) ↔
        IsEmpty (SimpleGraph.pathGraph 4 ↪g G) ∧
        IsEmpty (SimpleGraph.fromEdgeSet
          ({s(1, 2), s(0, 3), s(1, 3), s(2, 3)} : Set (Sym2 (Fin 4))) ↪g G))) ∧
    (∀ (V : Type) [Finite V] (J : SimpleGraph V) (m : ℕ) (e : Fin m ≃ J.edgeSet),
      Useless a (matchFam J e) ↔
        ∀ C : J.lineGraph.ConnectedComponent, C.toSimpleGraph.IsCompleteMultipartite) ∧
    (∃ J : SimpleGraph (Fin 5), J.IsTree ∧
      ∃ (m : ℕ) (e : Fin m ≃ J.edgeSet), HasGap a (matchFam J e)) := by sorry

end LDPSelect.Supplement
