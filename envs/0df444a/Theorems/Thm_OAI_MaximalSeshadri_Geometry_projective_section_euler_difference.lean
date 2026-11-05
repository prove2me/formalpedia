-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_section_euler_difference
-- name    : OAI.MaximalSeshadri.Geometry.projective_section_euler_difference
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:03.56465+00:00
-- url     : https://prove2.me/theorems/72df722b-ca44-4479-8fdf-51f8bc551a0f
-- title:
--   Euler difference on a curve as the length of a cokernel
-- statement:
--   On a projective curve $X$ over $\mathbb C$ with a line bundle $L$ and a nonzero section $s$: $\chi(L)-\chi(\mathcal O_X)$ equals the $\mathbb C$-dimension of the global sections of the cokernel of $s:\mathcal O_X\to L$.
--
--   **Notation.** $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_section_euler_difference`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SectionEuler.lean#L96

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Cohomology
noncomputable section
open CategoryTheory CategoryTheory.Abelian

end
end MaximalSeshadri.Cohomology

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem projective_section_euler_difference {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) =
      letI := Module.compHom Γ(cokernel s, ⊤) (baseScalars p)
      (Module.finrank ℂ Γ(cokernel s,⊤) : ℤ) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
