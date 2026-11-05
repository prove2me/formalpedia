-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_relationCycles_edge0_C
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge0_C
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:15.297106+00:00
-- url     : https://prove2.me/theorems/737ef15e-a4f9-4d96-badb-e69c7d289bd9
-- title:
--   Third component of the relation cycle for the first edge
-- statement:
--   In the plane-cover setting, let $x$ lie in `planePair k s L 0 1 ⊓ planePair k s L 0 2` and let $f$ be a morphism from the free module on the iso-open of $s_0$ to $L$ with chart value $x$. Then the third component of `relationCycles` applied to `planeRelIota s ≫ biprod.desc f (biprod.desc 0 0)` is zero.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `planeVertex` and `planePair` are the images in the sections over the triple overlap (`planeTriple`) of sections over the chart of $s_i$, and over the overlap of the charts of $s_i,s_j$, respectively.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge0_C`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/PlaneBoundaries.lean#L175

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

theorem relationCycles_edge0_C (x : ↥(planePair k s L 0 1 ⊓ planePair k s L 0 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 0))) L.sheaf)
    (_hf : homChart k L.sheaf (planeTriple_le s 0) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) f (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 0))).val.2.2.val = 0 := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections
end
end OAI
