-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_eq_of_combination
-- name    : OAI.MaximalSeshadri.Projective.sectionIdeal_eq_of_combination
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:18:00.819044+00:00
-- url     : https://prove2.me/theorems/8280a060-075a-41ef-a9b7-b12e17143198
-- title:
--   Section ideals depend only on the linear combination
-- statement:
--   Let $K$ be a field, $X$ a scheme, $s$ and $t$ finite families of sections of a module $M$ whose iso-opens cover $X$, and $v,w$ coefficient vectors with $\sum_j k(v_j)s_j=\sum_j k(w_j)t_j$. Then `sectionIdeal k s hs v` = `sectionIdeal k t ht w`.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.sectionIdeal_eq_of_combination`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SectionIdealExt.lean#L27

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
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] [Fintype τ] {X : Scheme}

theorem sectionIdeal_eq_of_combination {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (t : τ → (O X ⟶ M)) (ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤)
    (v : σ → K) (w : τ → K) (heq : sectionCombination k s v = sectionCombination k t w) :
    sectionIdeal k s hs v = sectionIdeal k t ht w := by
  sorry

end
end MaximalSeshadri.Projective
end
end
end
end OAI
