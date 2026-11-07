-- Prove2me | Theorems.Thm_FourColorLinear_eq_2_3_4
-- name    : FourColorLinear.eq_2_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:15.606227+00:00
-- url     : https://prove2.me/theorems/38c63c50-feee-4dad-a711-e0297e8ff88d
-- title:
--   The identities (2), (3), (4) of the bottom-up and top-down processing
-- statement:
--   Let $R$ be a non-leaf region of a recursive division of a triangulation $G$, with children $R_1,\dots,R_d$, and let $\psi$ be a coloring of the colored part with a color pairing. With $\mathcal K$ the Kempe edges and $B'=\bigcup_j\partial R_j$, $B=\partial R\cup B'$:
--   $$\partial R^{\mathcal K}_R=\partial R^{\mathcal K}_{H},\qquad H=\bigcup_j\partial R_{j\,R_j}^{\ \mathcal K}=(B')^{\mathcal K}_R,\tag{2}$$
--   $$\partial R_{j\,G-E(R_j)}^{\ \mathcal K}=\partial R_{j\,B^{\mathcal K}_{G-E(R_j)}}^{\ \mathcal K},\qquad B^{\mathcal K}_{G-E(R_j)}=B^{\mathcal K}_{\partial R^{\mathcal K}_{G-E(R)}\cup\bigcup_{h\ne j}\partial R_{h\,R_h}^{\ \mathcal K}},\tag{3}$$
--   $$(B')^{\mathcal K}_G=\partial R^{\mathcal K}_{G-E(R)}\cup\bigcup_j\partial R_{j\,R_j}^{\ \mathcal K},\tag{4}$$
--   and $\partial R\subseteq B'$, so $B=B'$.
--
--   These identities are the recursion by which boundary graphs are computed from the graphs of the parent and the children, in time proportional to the boundaries.
--
--   Differences from the source:
--   - reading: "=" between plane graphs → equal attachment edges at the same places in the rotation at each original vertex, and the same Kempe nodes: an isomorphism fixing the original vertices; reason: the strongest reading the construction determines; rotation around a Kempe node is left out, because the construction does not fix it when the component has a cycle
--   - encoding: (B)^K_{a union of contractions} → an explicit contraction of the attachment edges and Kempe nodes of the pieces, in the faces of B; reason: the construction of p.15 applied to the union of p.15
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), (2) p.15; (3), (4) p.17

import Mathlib
import Definitions.Def_FourColorLinear_contr
import Definitions.Def_FourColorLinear_IsRegion
import Definitions.Def_FourColorLinear_IsKempeChangeOn

open PlanarQueue.Genus

namespace FourColorLinear

/-- The identities (2), (3), (4) of arXiv:2610.39753 (held version, sha256 4dce39c5…), pp.15, 17:
"∂R^K_R = ∂R^K_H where H = ∪_{j=1}^d ∂Rj^K_{Rj} = (∪_{j=1}^d ∂Rj)^K_R. (2)";
"∂Rj^K_{G−E(Rj)} = ∂Rj^K_{B^K_{G−E(Rj)}} where B^K_{G−E(Rj)} = B^K_{∂R^K_{G−E(R)} ∪ ⋃_{h≠j} ∂Rh^K_{Rh}} (3)",
with `B = ∂R ∪ ⋃_j ∂Rj`; and "B^K_G = ∂R0^K_{G−E(R0)} ∪ ⋃_{j=1}^d ∂Rj^K_{Rj}. (4)" with `B = ⋃_j ∂Rj`.

**Formalization Note** `=` is equality of `CRes`: the same attachment edges at the same places in the
rotation at each original vertex, ending at the same Kempe nodes. This is an isomorphism fixing the
original vertices, not only equal connectivity. Rotation around a Kempe node is not determined by the
paper when its component has a cycle, and is left out. `R` is a non-leaf region of a recursive
division of a triangulation with a coloring of the colored part `W`. `∂R ⊆ ⋃_j ∂Rj`, as p.17 notes, is
the last clause. -/
theorem eq_2_3_4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (S : EmbeddingScheme G)
    (hS : IsPlaneTriangulation S) (D : RecDiv n) (hD : IsRecursiveDivision S D)
    (W : Set (Fin n)) (ψ : Fin n → Fin 4) (hψ : ProperOn G W ψ) (p : Fin 3)
    (i a : ℕ) (hi : i < D.h) (ha : a < D.count (i + 1)) :
    let K := kempeEdges G W ψ p
    let ι := {j // j ∈ D.children i a}
    let R := D.region (i + 1) a
    let Rj : ι → Set (Sym2 (Fin n)) := fun j => D.region i j.1
    let dR := boundaryEdges S R
    let dRj : ι → Set (Sym2 (Fin n)) := fun j => boundaryEdges S (Rj j)
    let Bc : Set (Sym2 (Fin n)) := ⋃ j, dRj j
    let B : Set (Sym2 (Fin n)) := dR ∪ Bc
    -- (2)
    contr S K (edgeVerts dR) dR R =
        contr2 S K (edgeVerts dR) dR (fun j => edgeVerts (dRj j)) dRj Rj ∧
    contr S K (edgeVerts Bc) Bc R =
        cUnion S K Bc (fun j => edgeVerts (dRj j)) dRj Rj ∧
    -- (3)
    (∀ j : ι,
      contr S K (edgeVerts (dRj j)) (dRj j) (Rj j)ᶜ =
          contr2 S K (edgeVerts (dRj j)) (dRj j) (fun _ : Unit => edgeVerts B) (fun _ => B)
            (fun _ => (Rj j)ᶜ) ∧
      contr S K (edgeVerts B) B (Rj j)ᶜ =
          contr2 S K (edgeVerts B) B
            (fun o : Option {h : ι // h ≠ j} => o.elim (edgeVerts dR) fun h => edgeVerts (dRj h.1))
            (fun o => o.elim dR fun h => dRj h.1)
            (fun o => o.elim Rᶜ fun h => Rj h.1)) ∧
    -- (4)
    contr S K (edgeVerts Bc) Bc Set.univ =
        cUnion S K Bc
          (fun o : Option ι => o.elim (edgeVerts dR) fun h => edgeVerts (dRj h))
          (fun o => o.elim dR dRj)
          (fun o => o.elim Rᶜ Rj) ∧
    dR ⊆ Bc := by sorry

end FourColorLinear
