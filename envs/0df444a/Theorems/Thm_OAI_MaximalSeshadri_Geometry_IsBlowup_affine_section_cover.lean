-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IsBlowup_affine_section_cover
-- name    : OAI.MaximalSeshadri.Geometry.IsBlowup.affine_section_cover
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:56.123786+00:00
-- url     : https://prove2.me/theorems/582291c0-574c-4812-a61c-a8328a69d291
-- title:
--   Affine section cover of a blow-up of an affine scheme
-- statement:
--   Let $X$ be an affine scheme, $I$ an ideal sheaf on $X$, and $\pi:B\to X$ a blow-up of $I$. If the line bundle $J$ with $\iota:J\to\mathcal O_B$ presents the pullback of $I$, then there is a family of sections of $J$ whose iso-opens cover $B$ and are all affine.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IsBlowup.affine_section_cover`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupAffineSections.lean#L46

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames

variable {X B B' : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.affine_section_cover [IsAffine X] (hπ : IsBlowup I π)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ (α : Type) (s : α → (O B ⟶ J.sheaf)),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
