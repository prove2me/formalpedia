-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_finite_plane_H1
-- name    : OAI.MaximalSeshadri.Projective.finite_plane_H1
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:27.602197+00:00
-- url     : https://prove2.me/theorems/6c96df35-6b2d-43d1-9e33-2d322a96c6f8
-- title:
--   Finiteness of the toric H^1 quotient for a plane cover
-- statement:
--   Let $K$ be a field, $k:K\to\Gamma(X,\top)$, and $s=(s_0,s_1,s_2)$ sections of a module $M$ with iso-opens covering $X$ such that `sectionsMorphism k s hs` to the plane is finite. For a line bundle $L$, the quotient of `cycles` by `vertexBoundaries` of the edge submodules `planePair` and vertex submodules `planeVertex` inside the sections over the triple overlap is finite-dimensional over $K$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$. `cycles A B C` is the submodule of $A\times B\times C$ of triples with zero sum. `planeVertex` and `planePair` are the images in the sections over the triple overlap (`planeTriple`) of sections over the chart of $s_i$, and over the overlap of the charts of $s_i,s_j$, respectively.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.finite_plane_H1`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneH1Finite.lean#L21

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

theorem finite_plane_H1 (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K ((cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)) ⧸
      vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
        (planeVertex k s L)) := by
  sorry

end
end MaximalSeshadri.Projective
end
end OAI
