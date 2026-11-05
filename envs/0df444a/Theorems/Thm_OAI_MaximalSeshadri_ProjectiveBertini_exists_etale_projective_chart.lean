-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_ProjectiveBertini_exists_etale_projective_chart
-- name    : OAI.MaximalSeshadri.ProjectiveBertini.exists_etale_projective_chart
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:18:03.632191+00:00
-- url     : https://prove2.me/theorems/5d93dd0b-a180-421b-aead-86103c4929c6
-- title:
--   Étale projective charts at any point
-- statement:
--   Let $K$ be a field, $X$ integral, smooth of relative dimension 2 over $K$, with a closed immersion $h$ to $\operatorname{Proj}K[\sigma]$ over $K$. For $i\in\sigma$, an open $W$, and $x\in W$ with $h(x)$ in the basic open of $x_i$, there is an `EtaleProjectiveChart` of $g,h$ with $x$ in its affine open, contained in $W$, with coordinate $i$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.ProjectiveBertini.exists_etale_projective_chart`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/ProjectiveRefinement.lean#L58

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

theorem exists_etale_projective_chart [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (W : X.Opens) (x : X) (hxW : x ∈ W)
    (hxi : h x ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  sorry

end
end MaximalSeshadri.ProjectiveBertini
end
end
end OAI
