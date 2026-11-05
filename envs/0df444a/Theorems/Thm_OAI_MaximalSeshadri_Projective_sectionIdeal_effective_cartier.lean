-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_effective_cartier
-- name    : OAI.MaximalSeshadri.Projective.sectionIdeal_effective_cartier
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:14.766947+00:00
-- url     : https://prove2.me/theorems/1ab7d90e-fab3-4ed4-964a-9d4f56398b31
-- title:
--   Section ideals are effective Cartier
-- statement:
--   Let $X$ be integral, $L$ a line bundle, and $s$ a finite family of sections with iso-opens covering $X$ and nonzero combination $\sum_j k(v_j)s_j$. Then `sectionIdeal k s hs v` pulls back along the identity to an invertible ideal.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.sectionIdeal_effective_cartier`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CartierSection.lean#L68

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem sectionIdeal_effective_cartier [IsIntegral X] (L : LineBundle X)
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    InvertiblePullbackIdeal (sectionIdeal k s hs v) (𝟙 X) := by
  sorry

end
end MaximalSeshadri.Projective
end
end
end
end OAI
