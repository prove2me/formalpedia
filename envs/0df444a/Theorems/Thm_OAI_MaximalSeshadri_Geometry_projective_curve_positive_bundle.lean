-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_positive_bundle
-- name    : OAI.MaximalSeshadri.Geometry.projective_curve_positive_bundle
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:07.552801+00:00
-- url     : https://prove2.me/theorems/442aea3e-e90e-41fa-90d1-eaf5d86c68ae
-- title:
--   A positive line bundle with a section on a projective curve
-- statement:
--   For $X$ integral Noetherian, $p:X\to\operatorname{Spec}\mathbb C$ proper with $\dim X=1$, and sections $a$ of a module $A$ giving a closed immersion, there are a line bundle $H$, a section $s$, and a point $x$ with $x$ in the iso-open of $s$ and $\chi(H)-\chi(\mathcal O_X)>0$.
--
--   **Notation.** $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_curve_positive_bundle`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/AllCurveDegree.lean#L27

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames MaximalSeshadri.SectionOpens
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
include hd a ha

theorem projective_curve_positive_bundle :
    ∃ (H : LineBundle X) (s : O X ⟶ H.sheaf) (x : X),
      x ∈ isoOpen s ∧ 0 < eulerCharacteristic p 1 H.sheaf - eulerCharacteristic p 1 (O X) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
