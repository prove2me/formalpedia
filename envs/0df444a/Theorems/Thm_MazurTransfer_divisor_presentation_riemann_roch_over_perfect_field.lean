-- Prove2me | Theorems.Thm_MazurTransfer_divisor_presentation_riemann_roch_over_perfect_field
-- name    : MazurTransfer.divisor_presentation_riemann_roch_over_perfect_field
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T23:22:13.27746+00:00
-- url     : https://prove2.me/theorems/77f2aaac-23a1-4346-b23c-596c084ef220
-- title:
--   Full Riemann–Roch for divisor presentations over a perfect field
-- statement:
--   Let $X$ be a proper smooth integral curve over a perfect field $K$, and assume that its actual function field $F$ has full constant field $K$. Let $M$ have a compatible injective rational-section presentation by a divisor $D$, whose local images are the divisor Riemann–Roch spaces. For any cover $\mathcal V$ by two affine opens, its actual Čech cohomology groups are finite-dimensional and satisfy
--   \[\dim_K H^0(X,M)=\ell(D),\qquad\dim_K H^1(X,M)=i(D),\]
--   \[\chi_K(M)=\deg D+1-g(F).\]
--   Here $i(D)$ is the arithmetic index of specialty and $g(F)$ is the actual function-field genus. No algebraic-closure hypothesis is imposed. This connects numerical degree with actual sheaf cohomology in the arithmetic Picard correspondence used by the Mazur campaign; rational rank and reduction remain separate contracts.
-- source:
--   Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked perfect-field adaptation by Vas and contributors, downstream MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c .

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

theorem MazurTransfer.divisor_presentation_riemann_roch_over_perfect_field.{u}
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)) :
    letI := (baseToFunctionField x).toAlgebra
    Module.Finite K (𝒱.sectionsOf x M).H0 ∧ Module.Finite K (𝒱.sectionsOf x M).H1 ∧
      Module.finrank K (𝒱.sectionsOf x M).H0 = ell D ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = indexOfSpecialty D ∧
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1
        = Divisor.degree D + 1 - genusFF K X.functionField := by sorry
