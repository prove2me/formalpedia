-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_planeVertex_cross_clearing
-- name    : OAI.MaximalSeshadri.Projective.planeVertex_cross_clearing
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:06.879878+00:00
-- url     : https://prove2.me/theorems/ea879e2b-6659-41ff-a19f-0ee8529d9d67
-- title:
--   Clearing denominators between vertices
-- statement:
--   In the setting of the plane cover with affine charts and Laurent module on the triple overlap, every $x\in$ `planeVertex k s L j` admits $d\in\mathbb N$ with $T^{d(w_j-w_i)}\cdot x\in$ `planeVertex k s L i`.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `planeVertex` and `planePair` are the images in the sections over the triple overlap (`planeTriple`) of sections over the chart of $s_i$, and over the overlap of the charts of $s_i,s_j$, respectively.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.planeVertex_cross_clearing`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneVertex.lean#L36

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

theorem planeVertex_cross_clearing (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (haff : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i)))
    (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i j x, x ∈ planeVertex k s L j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ planeVertex k s L i := by
  sorry

end
end MaximalSeshadri.Projective
end
end OAI
