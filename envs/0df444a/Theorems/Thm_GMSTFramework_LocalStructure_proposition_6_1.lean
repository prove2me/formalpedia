-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_proposition_6_1
-- name    : GMSTFramework.LocalStructure.proposition_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:04:19.213197+00:00
-- url     : https://prove2.me/theorems/f3d73670-2704-477d-a4da-6d7c05d02470
-- title:
--   Proposition 6.1 — polynomial Flat Wall Theorem [GSW25b]: a $K_t$-model with $\mathcal T_\mu\subseteq\mathcal T_M$, or $\le t^2-t$ apices and a flat $n'$-submesh; $O(t^2|E|)$ algorithm
-- statement:
--   (Cited from [GSW25b] as printed in this paper.) For all integers $t\ge5$, $n'\ge2$, with $k=t^2-t$ and $n=7t^2n'+535t^3+44t^2\in O(t^2(n'+t))$: for every graph $G$ with an $n$-mesh $M\subseteq G$, either there is a $K_t$-minor-model $\mu$ with $\mathcal T_\mu$ a truncation of $\mathcal T_M$, or there are an $n'$-submesh $M'\subseteq M$ and $Z\subseteq V(G)\setminus V(M')$ with $|Z|\le k$ such that $M'$ is a flat mesh in $G-Z$. Furthermore there is an $O(t^2|E(G)|)$-time algorithm finding $\mu$ or $(M',Z)$ together with a sphere-rendition of $G-Z$ witnessing the flatness of $M'$.
--
--   Differences from the source:
--   - encoding: "there exists an algorithm … in time O(t²|E(G)|)" → one program P of the published word-RAM with oracle (CapacitatedKMedianFPT.Main: RunsTo, word-RAM time wordTime with the input word length, oracle calls counted separately) and one constant, for all inputs; the input is the self-delimiting encoding of the parameters, the labelled graph and the given objects (every description of a given cycle/rendition is accepted), and the output is a certificate (cell records of a rendition, vertex lists of paths, cycles, branch sets) of an object satisfying the conclusion; reason: topological objects cannot be input or output; the certificate fixes the combinatorial content and the conclusion asserts that a valid object realizing it exists; O(·) is a bound C·f with C independent of the input
--   - encoding: an n-mesh M ⊆ G (a graph) → a Mesh structure (its horizontal and vertical paths, each walked from the first to the last crossing path); reason: every mesh has such presentations and no notion used depends on the choice
--   - encoding: "k = t² − t", "n ∈ O(t²(n′ + t))" → k and n written out; the O-claim as ∃ C, ∀ t ≥ 5, n′ ≥ 2, n ≤ C·t²(n′ + t); reason: the integers are explicit in the statement
--   - encoding: the trace of the perimeter (curves "pushed slightly") → a trace relation (`IsTraceCycle`); flatness asks for some trace; reason: every property used is invariant under the push
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Proposition 6.1, p. 48 (PDF 51)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Algorithms

open scoped Classical
open CapacitatedKMedianFPT.Main

namespace GMSTFramework.LocalStructure

/-- Proposition 6.1 ([GSW25b], polynomial Flat Wall Theorem), with the size bound and the
algorithm. -/
theorem proposition_6_1 :
    (∃ C : ℕ, ∀ t n' : ℕ, 5 ≤ t → 2 ≤ n' →
      7 * t ^ 2 * n' + 535 * t ^ 3 + 44 * t ^ 2 ≤ C * (t ^ 2 * (n' + t))) ∧
    (∀ t n' : ℕ, 5 ≤ t → 2 ≤ n' →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (M : Mesh G (7 * t ^ 2 * n' + 535 * t ^ 3 + 44 * t ^ 2)
          (7 * t ^ 2 * n' + 535 * t ^ 3 + 44 * t ^ 2)),
        (∃ μ : (SimpleGraph.completeGraph (Fin t)).Minor G,
            IsTruncation (tangleOfModel μ) M.tangle) ∨
        (∃ (M' : Mesh G n' n') (Z : Finset V), M'.IsSubmeshOf M ∧ Disjoint (Z : Set V) ↑M'.verts ∧
            Z.card ≤ t ^ 2 - t ∧ IsFlatMesh (minusVerts G Z) M')) ∧
    (∃ (P : Program) (C : ℕ), ∀ t n' : ℕ, 5 ≤ t → 2 ≤ n' →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (label : V ≃ Fin (Fintype.card V))
        (M : Mesh G (7 * t ^ 2 * n' + 535 * t ^ 3 + 44 * t ^ 2)
          (7 * t ^ 2 * n' + 535 * t ^ 3 + 44 * t ^ 2)),
        ∃ out : List ℚ,
          RunsWithin P zeroOracle
            (encNats [t, n'] ++ encGraph G (fun _ => ∅) label ++ encMesh label M) out
            (C * (t ^ 2 * G.edgeSet.ncard)) 0 ∧
          ((∃ (μ : (SimpleGraph.completeGraph (Fin t)).Minor G) (bs : List (List ℕ)),
              IsTruncation (tangleOfModel μ) M.tangle ∧
              DescribesModel label (Fintype.equivFin (Fin t)) μ bs ∧ out = [0] ++ encNested bs) ∨
           (∃ (M' : Mesh G n' n') (Z : Finset V) (ρ : Rendition TheSphere (minusVerts G Z))
              (cells : List (List ℕ)),
              M'.IsSubmeshOf M ∧ Disjoint (Z : Set V) ↑M'.verts ∧ Z.card ≤ t ^ 2 - t ∧
              WitnessesFlatMesh ρ M' ∧ DescribesRendition label ρ cells ∧
              out = [1] ++ encMesh label M' ++ encNats (namesOf label (Z : Set V)) ++
                encNested cells))) := by sorry

end GMSTFramework.LocalStructure
