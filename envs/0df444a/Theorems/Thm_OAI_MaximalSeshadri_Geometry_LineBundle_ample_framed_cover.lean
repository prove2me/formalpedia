-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_ample_framed_cover
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.ample_framed_cover
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T18:45:35.7171+00:00
-- url     : https://prove2.me/theorems/87dce57d-a27a-4da4-b78a-09c3c82034b9
-- title:
--   An ample line bundle admits a finite framed affine section cover
-- statement:
--   Let $X$ be a compact scheme, let $L$ be an ample line bundle, and let $M$ be any line bundle. For every positive integer $a$, there is a positive multiple $d$ of $a$ and a finite family of global sections of $L^d$ whose nonvanishing loci cover $X$, are affine and nonempty, and on each of which $M$ is trivialized.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; declaration `OAI.MaximalSeshadri.Geometry.LineBundle.ample_framed_cover`, `lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/AmpleFramedCover.lean`, lines 17-24, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/AmpleFramedCover.lean#L17-L24

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.ample_framed_cover [CompactSpace X] (L M : LineBundle X)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ d : ℕ, 0 < d ∧ a ∣ d ∧ ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ s : ι → GlobalSections X (L.pow d).sheaf,
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) ∧
        (∀ i, Nonempty (M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme)) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
