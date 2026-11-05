-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_exists_centered_embedding
-- name    : OAI.MaximalSeshadri.Projective.exists_centered_embedding
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:31.618068+00:00
-- url     : https://prove2.me/theorems/c593974b-7cdf-4df9-8138-73df8e60322b
-- title:
--   A projective embedding centered at a point
-- statement:
--   Let $K$ be algebraically closed, $X$ integral, and $s$ sections indexed by $\operatorname{Option}\sigma$ with iso-opens covering $X$ defining a closed immersion. There are such sections $t$ giving a closed immersion, and a point $y$ with $x\notin$ `centeredOpen t` if and only if $x=y$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$. `centeredOpen s` is the union of the iso-opens of $s_{\mathrm{some}\,i}$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.exists_centered_embedding`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/CenteredEmbedding.lean#L41

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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem exists_centered_embedding [IsIntegral X] [IsAlgClosed K] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] :
    ∃ t : Option σ → (O X ⟶ M), ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
      IsClosedImmersion (sectionsMorphism k t ht) ∧
      ∃ y : X, ∀ x : X, x ∉ centeredOpen t ↔ x = y := by
  sorry

end
end MaximalSeshadri.Projective
end
end
end
end OAI
