-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_H0_finite
-- name    : OAI.MaximalSeshadri.Geometry.projective_curve_H0_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:10.243079+00:00
-- url     : https://prove2.me/theorems/e623c3e0-c15c-4d8a-94f1-dbe9ee499f2d
-- title:
--   Finiteness of global sections on projective curves
-- statement:
--   With $K$ an infinite field and $X$ an integral Noetherian projective curve over $K$ as above, for every line bundle $L$ the space $H^0(X,L)=\operatorname{Ext}^0(\mathcal O_X,L)$ is finite-dimensional over $K$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_curve_H0_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/CurveH0Finite.lean#L115

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem projective_curve_H0_finite {σ : Type} [Fintype σ] [Infinite K]
    [IsIntegral X] [IsNoetherian X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf 0) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
