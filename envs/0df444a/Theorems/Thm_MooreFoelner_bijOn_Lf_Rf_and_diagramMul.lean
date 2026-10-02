-- Prove2me | Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
-- name    : MooreFoelner.bijOn_Lf_Rf_and_diagramMul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:34:35.191981+00:00
-- url     : https://prove2.me/theorems/fd8e9616-4d0d-4b4f-aa06-2e02aa1fe55c
-- title:
--   §2 — f ↦ (L_f, R_f) is an isomorphism from F onto the reduced tree diagrams with the product ‘f followed by g’
-- statement:
--   The product $D \cdot D'$ of two reduced tree diagrams (`diagramMul`) is a reduced tree diagram whose map on infinite sequences is the map of $D$ followed by the map of $D'$; on reduced tree diagrams this product is associative, the trivial diagram $(\{\langle\rangle\}, \{\langle\rangle\})$ is reduced and is a two-sided identity, and the reverse $(R, L)$ of a reduced diagram $(L, R)$ is reduced and is its two-sided inverse; the map $f \mapsto (L_f, R_f)$ is a bijection from Moore's $F$ onto the set of reduced tree diagrams; each $(L_f, R_f)$ describes $f$; and for all $f, g$ in $F$, $(L_{f \cdot g}, R_{f \cdot g})$ is the product $(L_f, R_f) \cdot (L_g, R_g)$. So the reduced tree diagrams form a group under this product and $f \mapsto (L_f, R_f)$ is an isomorphism from $F$ onto it, which is Moore's definition of $F$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 4, §2 (definition of F)

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem bijOn_Lf_Rf_and_diagramMul :
    (∀ D D' : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 → IsReducedDiagram D'.1 D'.2 →
        IsReducedDiagram (diagramMul D D').1 (diagramMul D D').2 ∧
          ∀ x, diagramMap (diagramMul D D').1 (diagramMul D D').2 x =
            diagramMap D'.1 D'.2 (diagramMap D.1 D.2 x)) ∧
    (∀ D D' D'' : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 → IsReducedDiagram D'.1 D'.2 →
        IsReducedDiagram D''.1 D''.2 →
        diagramMul (diagramMul D D') D'' = diagramMul D (diagramMul D' D'')) ∧
    IsReducedDiagram trivialTree trivialTree ∧
    (∀ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 →
        diagramMul (trivialTree, trivialTree) D = D ∧ diagramMul D (trivialTree, trivialTree) = D) ∧
    (∀ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 →
        IsReducedDiagram D.2 D.1 ∧ diagramMul D (D.2, D.1) = (trivialTree, trivialTree) ∧
          diagramMul (D.2, D.1) D = (trivialTree, trivialTree)) ∧
    Set.BijOn (fun f : MooreF => (Lf (toMap f), Rf (toMap f))) Set.univ
        {D : Finset Seq × Finset Seq | IsReducedDiagram D.1 D.2} ∧
      (∀ f : MooreF, Describes (Lf (toMap f)) (Rf (toMap f)) (toMap f)) ∧
      ∀ f g : MooreF, (Lf (toMap (f * g)), Rf (toMap (f * g))) =
        diagramMul (Lf (toMap f), Rf (toMap f)) (Lf (toMap g), Rf (toMap g)) := by
  sorry

end MooreFoelner
