-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_lift_section_of_local_ideal_power
-- name    : OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:55.044402+00:00
-- url     : https://prove2.me/theorems/f996a68b-5a64-4642-b326-b56a0a19531a
-- title:
--   Lifting sections with local ideal-power coefficients
-- statement:
--   Let $f:Y\to X$, $I$ an ideal sheaf on $X$, and $J,\iota$ presenting $f^{-1}I$. Let $M$ be a line bundle on $X$, $n\in\mathbb N$, and $s$ a section of $M$ whose coefficients locally lie in $I^n$ on affine frames. Then there is a unique section $q$ of $J^n\otimes f^*M$ whose image in $f^*M$ under the inclusion is $f^*s$.
--
--   **Notation.** `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IdealSectionLifting.lean#L88

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

theorem lift_section_of_local_ideal_power (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (M : LineBundle X) (n : ℕ) (s : O X ⟶ M.sheaf)
    (hs : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ e : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme,
        affineCoefficient V e s ∈ (I.ideal V)^n) :
    ∃! q : O Y ⟶ ((J.pow n).tensor (M.pullback f)).sheaf,
      q ≫ tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) =
        pullbackSection f s := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
