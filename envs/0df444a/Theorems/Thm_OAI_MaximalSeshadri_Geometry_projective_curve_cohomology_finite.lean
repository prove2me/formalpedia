-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite
-- name    : OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:43.061056+00:00
-- url     : https://prove2.me/theorems/472f2718-4741-4a76-bca2-e4a2cc5dcc79
-- title:
--   Finite-dimensional cohomology of line bundles on projective curves
-- statement:
--   With $K$ an infinite field, $\sigma$ finite, $X$ integral Noetherian, $p:X\to\operatorname{Spec}K$ proper, $\dim X=1$, and sections giving a closed immersion to $\operatorname{Proj}K[\sigma]$: for a line bundle $L$ and every $n$, the $K$-module $\operatorname{Ext}^n(\mathcal O_X,L)$ is finite.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ProjectiveCurveCohomology.lean#L23

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem projective_curve_cohomology_finite
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf n) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
