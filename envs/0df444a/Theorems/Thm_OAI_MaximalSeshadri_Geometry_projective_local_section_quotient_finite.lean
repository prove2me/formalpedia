-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_local_section_quotient_finite
-- name    : OAI.MaximalSeshadri.Geometry.projective_local_section_quotient_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:09:53.131545+00:00
-- url     : https://prove2.me/theorems/ecf47605-fd58-47f6-84f0-1048ae8e2e15
-- title:
--   Local quotients by a section are finite
-- statement:
--   On a projective curve $X$ over $\mathbb C$, let $s\ne0$ be a section of a line bundle $L$, $f:Y\to X$ an open immersion with $Y$ affine, Noetherian, nonempty, and $e$ a trivialization of $L$ on $Y$. Then $\Gamma(Y)/(\text{coefficient of }s)$ is finite over $\mathbb C$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_local_section_quotient_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/LocalSectionDegree.lean#L134

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X Y : Scheme.{0}}

theorem projective_local_section_quotient_finite [IsIntegral X] [IsNoetherian X]
    {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    letI := Module.compHom
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
    Module.Finite ℂ (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
