-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PlaneBlowup_blowup_power_contraction
-- name    : OAI.MaximalSeshadri.PlaneBlowup.blowup_power_contraction
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:00.846664+00:00
-- url     : https://prove2.me/theorems/185a75f2-95a5-4a0f-ae81-b66afe8a6973
-- title:
--   Ideal power contraction for flat algebras over the plane
-- statement:
--   Let $K$ be a field, $A$ a flat algebra over the polynomial ring $K[x,y]$ (`PlaneRing K`), $J=(x,y)A$, and $\pi:B\to\operatorname{Spec}A$ a blow-up of the ideal sheaf of $J$. Then the image ideal under $\pi$ of the $m$-th power of the pullback of $J$ is the ideal sheaf of $J^m$.
--
--   **Notation.** `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.PlaneBlowup.blowup_power_contraction`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/PowerContraction.lean#L16

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct ReesGrading
open MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
variable (K : Type) [Field K]

theorem blowup_power_contraction {A : Type} [CommRing A] [Algebra (PlaneRing K) A]
    [Module.Flat (PlaneRing K) A]
    {B : Scheme} {π : B ⟶ Spec (CommRingCat.of A)}
    (hπ : IsBlowup (specIdeal ((originIdeal K).map (algebraMap (PlaneRing K) A))) π)
    (m : ℕ) :
    (((specIdeal ((originIdeal K).map (algebraMap (PlaneRing K) A))).comap π)^m).map π =
      specIdeal (((originIdeal K).map (algebraMap (PlaneRing K) A))^m) := by
  sorry

end
end MaximalSeshadri.PlaneBlowup
end
end OAI
