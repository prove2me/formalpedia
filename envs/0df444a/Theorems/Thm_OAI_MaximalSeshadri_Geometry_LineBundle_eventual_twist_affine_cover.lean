-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_eventual_twist_affine_cover
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.eventual_twist_affine_cover
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:54.83958+00:00
-- url     : https://prove2.me/theorems/dba56c53-354d-4d92-96dd-e3436e415545
-- title:
--   Eventual affine covers by twisted sections
-- statement:
--   Let $X$ be integral and compact, $P,J$ line bundles on $X$, and $t$ a family of sections of $P$ whose iso-opens cover $X$. Assume that over each iso-open of $t_i$ there is a family of sections of $J$ whose iso-opens cover it and are affine. Then there is $N$ such that for every $n\ge N$ there is a finite family of sections of $P^{n+1}\otimes J$ whose iso-opens cover $X$, are affine, and are nonempty.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.eventual_twist_affine_cover`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/EventualExceptionalAmple.lean#L22

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

theorem LineBundle.eventual_twist_affine_cover [IsIntegral X] [CompactSpace X]
    (P J : LineBundle X) {κ : Type} (t : κ → (O X ⟶ P.sheaf))
    (ht : (⨆ i,isoOpen (t i)) = ⊤)
    (hlocal : ∀ i, ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ (σ : Type) (_ : Fintype σ)
      (s : σ → (O X ⟶ ((P.pow (n+1)).tensor J).sheaf)),
        (⨆ a,isoOpen (s a)) = ⊤ ∧
        (∀ a, IsAffineOpen (isoOpen (s a))) ∧
        (∀ a, (isoOpen (s a) : Set X).Nonempty) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
