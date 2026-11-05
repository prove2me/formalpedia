-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_section_H2_untwist
-- name    : OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:23.348179+00:00
-- url     : https://prove2.me/theorems/d21470bd-b56a-4614-9cec-2b92eddd62e7
-- title:
--   Comparing H^2 across a section of a generated bundle
-- statement:
--   Let $S$ be a surface with ample $A$, $L,M$ line bundles, $s$ a finite family of sections of $L$ with iso-opens covering $S$, $v$ a coefficient vector with nonzero combination, and suppose the section ideal defines an integral curve $C$ of dimension one with $\deg_C(L\otimes M)\ge0$. Then $h^2(S,M)\le h^1(C,\mathcal O_C)+h^2(S,L\otimes M)$.
--
--   **Notation.** $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. $h^n$ is `cohomologyDimension`, the `Module.finrank` over $\mathbb C$ of $\operatorname{Ext}^n(\mathcal O,-)$, which is 0 for an infinite-dimensional space. The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH2Untwist.lean#L26

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem generated_section_H2_untwist (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle S.scheme)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (hdeg : let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
      0 ≤ curveDegree S (L.tensor M) C) :
    cohomologyDimension S.structureMap M.sheaf 2 ≤
      cohomologyDimension ((sectionIdeal k s hs v).subschemeι ≫ S.structureMap)
        (O (sectionIdeal k s hs v).subscheme) 1 +
      cohomologyDimension S.structureMap (L.tensor M).sheaf 2 := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
