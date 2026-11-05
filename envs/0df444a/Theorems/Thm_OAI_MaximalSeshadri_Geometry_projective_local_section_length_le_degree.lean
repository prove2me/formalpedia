-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_local_section_length_le_degree
-- name    : OAI.MaximalSeshadri.Geometry.projective_local_section_length_le_degree
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:03.381843+00:00
-- url     : https://prove2.me/theorems/2103628d-652d-4be2-9635-46d85850eb20
-- title:
--   Local length of a section is at most the degree
-- statement:
--   In the setting of the previous statement, the $\mathbb C$-dimension of $\Gamma(Y)/(\text{coefficient of }s)$ is at most $\chi(L)-\chi(\mathcal O_X)$.
--
--   **Notation.** $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_local_section_length_le_degree`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/LocalSectionDegree.lean#L157

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

theorem projective_local_section_length_le_degree [IsIntegral X] [IsNoetherian X]
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
    (Module.finrank ℂ (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) : ℤ) ≤
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
