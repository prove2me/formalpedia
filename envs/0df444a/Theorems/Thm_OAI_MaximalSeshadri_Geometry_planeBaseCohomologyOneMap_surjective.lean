-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_planeBaseCohomologyOneMap_surjective
-- name    : OAI.MaximalSeshadri.Geometry.planeBaseCohomologyOneMap_surjective
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:37.926933+00:00
-- url     : https://prove2.me/theorems/731b5b4d-94ff-47f0-9a61-ef141c355fc3
-- title:
--   Surjectivity onto H^1 from the plane relation quotient
-- statement:
--   For a Noetherian scheme $X$ and sections $s_0,s_1,s_2$ with affine iso-opens covering $X$, and a line bundle $L$, the map `planeBaseCohomologyOneMap` from the quotient of $\operatorname{Hom}$ from the relation module to $L$ by the relation boundaries to $\operatorname{Ext}^1(\mathcal O_X,L)$ is surjective.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.planeBaseCohomologyOneMap_surjective`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH1Finite.lean#L69

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections ModuleFlasque ModuleMayerVietoris
open MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.instLinearCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopSheafOfModulesRingCatSheaf_definitions_1

attribute [local instance] OAI.MaximalSeshadri.Geometry.instHasExtSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheaf_definitions_1

attribute [local instance] baseHomModule

theorem planeBaseCohomologyOneMap_surjective [IsNoetherian X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i))) (L : LineBundle X) :
    Function.Surjective (planeBaseCohomologyOneMap k s hs h L) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
