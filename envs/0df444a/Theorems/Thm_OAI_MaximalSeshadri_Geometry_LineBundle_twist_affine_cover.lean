-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_twist_affine_cover
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.twist_affine_cover
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:47.092205+00:00
-- url     : https://prove2.me/theorems/9c761dc9-8db5-40d0-88b2-7265f5116795
-- title:
--   An affine cover by twisted sections
-- statement:
--   Let $X$ be integral and compact, $P,J$ line bundles, $t$ sections of $P$ with iso-opens covering $X$, and assume $J$ has affine covers by sections over each iso-open of $t_i$. Then there are $n>0$ and a finite family of sections of $P^n\otimes J$ whose iso-opens cover $X$, are affine and are nonempty.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.twist_affine_cover`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/RelativeProjectivity.lean#L22

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem LineBundle.twist_affine_cover [IsIntegral X] [CompactSpace X]
    (P J : LineBundle X) {κ : Type} (t : κ → (O X ⟶ P.sheaf))
    (ht : (⨆ i,isoOpen (t i)) = ⊤)
    (hlocal : ∀ i, ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a))) :
    ∃ n : ℕ, 0 < n ∧ ∃ (σ : Type) (_ : Fintype σ)
      (s : σ → (O X ⟶ ((P.pow n).tensor J).sheaf)),
        (⨆ a,isoOpen (s a)) = ⊤ ∧
        (∀ a, IsAffineOpen (isoOpen (s a))) ∧
        (∀ a, (isoOpen (s a) : Set X).Nonempty) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
