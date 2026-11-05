-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_local_affine_mixed_extension
-- name    : OAI.MaximalSeshadri.Geometry.local_affine_mixed_extension
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:08:49.092058+00:00
-- url     : https://prove2.me/theorems/bceb0106-c9d9-4041-b6e7-bcb5914cff84
-- title:
--   Local extension of twisted sections over an affine open
-- statement:
--   Let $L,M$ be line bundles on a scheme $X$, $U$ an affine open with trivializations $e,d$ of $L,M$ on $U$, $s$ a section of $L$, $V\subset U$ the basic open of the coefficient of $s$, and $w\in\Gamma(V,M)$. Then there is $N$ such that for $n\ge N$ there is a section $t$ of $L^n\otimes M$ over $U$ whose restriction to $V$ equals $s^n\otimes w$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.local_affine_mixed_extension`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedLocalExtension.lean#L54

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

attribute [local instance] MaximalSeshadri.TensorPure.sectionModule

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

end
end MaximalSeshadri.TensorPure

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem local_affine_mixed_extension (L M : LineBundle X) (U : X.Opens) [IsAffine U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf)
    (w : Γ(M.sheaf, U.ι ''ᵁ (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι),
      let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
      (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
        (openSectionEquiv _ U t) =
      pure (L.pow n).sheaf M.sheaf (U.ι ''ᵁ V) ((powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) w := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
