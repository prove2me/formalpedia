-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_finite_plane_relation_quotient
-- name    : OAI.MaximalSeshadri.Geometry.finite_plane_relation_quotient
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:18:19.82476+00:00
-- url     : https://prove2.me/theorems/985ae3e0-7701-4189-ae3d-c57263db16d8
-- title:
--   Finiteness of the relation quotient for the plane cover
-- statement:
--   In the setting of a finite morphism to the plane given by $s_0,s_1,s_2$ on an integral $X$ with nonempty triple overlap, for a line bundle $L$ the quotient of $\operatorname{Hom}$ from `planeRelations s` to $L$ by `relationBoundaries k s L` is finite over $K$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.finite_plane_relation_quotient`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH1Finite.lean#L26

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

theorem finite_plane_relation_quotient [IsIntegral X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] [Nonempty (planeTriple s)] (L : LineBundle X) :
    Module.Finite K (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
