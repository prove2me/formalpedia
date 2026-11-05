-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_finite_projection_H0_finite
-- name    : OAI.MaximalSeshadri.Geometry.finite_projection_H0_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:11:51.562841+00:00
-- url     : https://prove2.me/theorems/219bc5d9-88d3-4ab4-9b78-2e604361b006
-- title:
--   H^0 is finite for a finite projection to the plane
-- statement:
--   Let $K$ be a field and $X$ integral with $s=(s_0,s_1,s_2)$ sections such that `sectionsMorphism k s hs` to the plane is finite, and with nonempty triple overlap. Then for a line bundle $L$, $\operatorname{Ext}^0(\mathcal O_X,L)$ is a finite $K$-module.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.finite_projection_H0_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH0Finite.lean#L44

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

theorem finite_projection_H0_finite [IsIntegral X]
    (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] [Nonempty (planeTriple s)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) k
    Module.Finite K (cohomology L.sheaf 0) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
