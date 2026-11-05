-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_dimension_le_one
-- name    : OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:18:23.115885+00:00
-- url     : https://prove2.me/theorems/2d6c9b40-c1b1-4f9c-af5a-e536a70df187
-- title:
--   Dimension of a section ideal's subscheme
-- statement:
--   Let $X$ be integral, smooth of relative dimension 2 over a field $K$, closed in a projective space over $K$. For a line bundle $L$ and sections $s$ with iso-opens covering $X$ and nonzero combination, the section ideal's subscheme has Krull dimension at most one.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SectionDimension.lean#L37

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem sectionIdeal_dimension_le_one [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    topologicalKrullDim (sectionIdeal k s hs v).subscheme ≤ 1 := by
  sorry

end
end MaximalSeshadri.Projective
end
end
end
end OAI
