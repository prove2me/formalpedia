-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_plane_boundaries_lift
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:05:04.605539+00:00
-- url     : https://prove2.me/theorems/56138f45-8e80-4dd3-9ef3-424d2de24b06
-- title:
--   Vertex boundaries lift to relation boundaries
-- statement:
--   In the plane-cover setting, the vertex boundaries of the edge submodules `planePair` and vertices `planeVertex` are contained in the image of `relationBoundaries k s L` under `relationCycles k s L`.
--
--   **Notation.** `planeVertex` and `planePair` are the images in the sections over the triple overlap (`planeTriple`) of sections over the chart of $s_i$, and over the overlap of the charts of $s_i,s_j$, respectively.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/PlaneBoundaries.lean#L284

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

section
variable {space : TopCat.{0}}
  (ringSheaf : Sheaf (Opens.grothendieckTopology space) RingCat.{0})
  (first second third : Opens space) {target : SheafOfModules ringSheaf}
  (morphism : tripleVertices ringSheaf first second third ⟶ target)

end

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.planeBoundariesLinear

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.planeBoundariesFreeHomGroup

attribute [local instance] baseHomModule
variable (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)

theorem plane_boundaries_lift :
    vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
      (planeVertex k s L) ≤ (relationBoundaries k s L).map (relationCycles k s L) := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections
end
end OAI
