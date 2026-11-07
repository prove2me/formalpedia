-- Prove2me | Theorems.Thm_FourColorLinear_lemma_10
-- name    : FourColorLinear.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:03.704229+00:00
-- url     : https://prove2.me/theorems/6e641dcc-373b-4ed2-83e3-6f703a32c2ec
-- title:
--   Lemma 10 — $B^{\mathcal K}_H$ is a plane graph of size $O(|B|)$ with the same Kempe connections
-- statement:
--   There is an absolute constant $C$ such that for each connected plane graph $P$, Kempe edges $K\subseteq E(P)$ and subgraphs $B$, $H$ of $P$, the contraction $B^{\mathcal K}_H$ of the Kempe edges of $H$ in the faces of $B$ satisfies:
--
--   1. it is a plane graph containing $B$, with each attachment edge at its appearance;
--   2. it has at most $C(|V(B)|+1)$ vertices and at most $C(|V(B)|+1)$ edges;
--   3. for all vertices $u,v$ of $B$,
--   $$u,v\text{ Kempe connected in }B\cup H\iff u,v\text{ Kempe connected in }B^{\mathcal K}_H.$$
--
--   All the identification of Kempe chains in $O(n/\log n)$ time goes through graphs of this form on boundaries.
--
--   Differences from the source:
--   - generalization: Kempe edges of a coloring → any set K of edges of P; reason: the proof uses nothing about K, and p.14 allows auxiliary Kempe edges; K from a coloring is a case
--   - reading: "B^K_H is a plane graph" → a rotation system on the darts of the result, agreeing with P on B and with each attachment edge at its appearance, with Euler genus 0; parallel attachment edges are allowed; reason: a vertex can appear twice on one face; the rotation at a Kempe node is existential, since the construction leaves it open when the component has a cycle
--   - encoding: size O(|B|) → at most C·(|V(B)| + 1) vertices and edges; reason: covers empty B; an isolated vertex of B also has a visit, which p.15's "twice the number of edges" does not count, and only the constant moves
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Lemma 10, p.15

import Mathlib
import Definitions.Def_FourColorLinear_contr

open PlanarQueue.Genus

namespace FourColorLinear

/-- Lemma 10 of arXiv:2610.39753 (held version, sha256 4dce39c5…), p.15: "Let BK_H be the contraction of the Kempe edges from H in the faces
of B. Then BK_H is a plane graph of size O(|B|) such that any two vertices in B are Kempe connected in
B ∪ H if and only if they are Kempe connected in BK_H."

**Formalization Note** `B` is `(Bv, Be)`, possibly with isolated vertices, each of which has an
appearance (a visit that p.15's "twice the number of edges" does not count; only the constant moves,
hence `|B| + 1`). `C` is absolute. Kempe connected means connected through `K`-edges. -/
theorem lemma_10 :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
      (S : EmbeddingScheme G), IsPlaneScheme S → G.Connected →
      ∀ (K : Set (Sym2 V)) (Bv : Set V) (Be H : Set (Sym2 V)),
        K ⊆ G.edgeSet → Be ⊆ G.edgeSet → H ⊆ G.edgeSet → edgeVerts Be ⊆ Bv →
        let r := contr S K Bv Be H
        IsPlaneContraction S Bv r ∧
        Bv.ncard + Nat.card r.Node ≤ C * (Bv.ncard + 1) ∧
        Be.ncard + r.attached.ncard ≤ C * (Bv.ncard + 1) ∧
        ∀ u ∈ Bv, ∀ v ∈ Bv,
          (SimpleGraph.fromEdgeSet ((Be ∪ H) ∩ K)).Reachable u v ↔
            (r.kempeGraph K).Reachable (.inl u) (.inl v) := by sorry

end FourColorLinear
