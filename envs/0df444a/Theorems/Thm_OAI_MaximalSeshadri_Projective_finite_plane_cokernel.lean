-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_finite_plane_cokernel
-- name    : OAI.MaximalSeshadri.Projective.finite_plane_cokernel
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:03.97484+00:00
-- url     : https://prove2.me/theorems/72e9cb8d-7baf-4178-a27f-ea2bf94338f8
-- title:
--   Finiteness of the cokernel on the triple overlap
-- statement:
--   Let $X$ be separated with sections $s$ defining a finite morphism to the plane as above. For a line bundle $L$, the quotient of the sections over the triple overlap by the sum of images of sections over the three double overlaps (`tripleBaseImage`) is finite-dimensional over $K$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.finite_plane_cokernel`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlanePairs.lean#L39

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

theorem finite_plane_cokernel [X.IsSeparated] (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K (Sections k L.sheaf (planeTriple s) ⧸
      tripleBaseImage k L.sheaf (SectionOpens.isoOpen (s 1))
        (SectionOpens.isoOpen (s 2)) (SectionOpens.isoOpen (s 0))) := by
  sorry

end
end MaximalSeshadri.Projective
end
end OAI
