-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_planePair_clearing
-- name    : OAI.MaximalSeshadri.Projective.planePair_clearing
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:08.58485+00:00
-- url     : https://prove2.me/theorems/4547e25b-c9b1-4b25-9053-4a566d28f502
-- title:
--   Clearing denominators from an edge to a vertex
-- statement:
--   For sections $s_0,s_1,s_2$ with affine iso-opens and a line bundle $L$, in the Laurent module on the triple overlap, every $x\in$ `planePair k s L i j` admits $d\in\mathbb N$ such that the Laurent monomial $T^{d(w_j-w_i)}$ moves $x$ into `planeVertex k s L i`, where $w_0=(0,0),w_1=(1,0),w_2=(0,1)$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `planeVertex` and `planePair` are the images in the sections over the triple overlap (`planeTriple`) of sections over the chart of $s_i$, and over the overlap of the charts of $s_i,s_j$, respectively.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.planePair_clearing`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlanePairToric.lean#L31

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

theorem planePair_clearing (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (haff : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i)))
    (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i j x, x ∈ planePair k s L i j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ planeVertex k s L i := by
  sorry

end
end MaximalSeshadri.Projective
end
end OAI
