-- Prove2me | Theorems.Thm_MomentComparison_polynomialGrowth_of_disk
-- name    : MomentComparison.polynomialGrowth_of_disk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:22:28.074799+00:00
-- url     : https://prove2.me/theorems/f88545c0-cba2-4dc5-9e6d-565e5df29170
-- title:
--   Moment Comparison: polynomial Growth of disk
-- statement:
--   Polynomial growth via a parametrization of the exterior. The map `g t / t`
--   parametrizes the exterior on the punctured disc. Multiplication by `t ^ d`
--   cancels the pole when the polynomial has degree at most `d`.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Conformal.lean#L34-L70
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Conformal.lean#L34-L70

module
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_MomentComparison_Lens
public import Definitions.Def_MomentComparison_ComplexPower
public import Definitions.Def_MomentComparison_LensAngle
public import Definitions.Def_MomentComparison_LensEvaluation
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_MomentComparison_Conformal
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Set Metric
open MomentComparison

theorem MomentComparison.polynomialGrowth_of_disk (P : Polynomial ℂ) {d : ℕ} (hP : P.natDegree ≤ d)
    {g : ℂ → ℂ} (hg : DiffContOnCl ℂ g (ball 0 1))
    {M : ℝ} (hbound : ∀ t ∈ sphere (0 : ℂ) 1, ‖P.eval (g t / t)‖ ≤ M)
    {t : ℂ} (ht : t ∈ closedBall 0 1) (ht0 : t ≠ 0) :
    ‖P.eval (g t / t)‖ ≤ ‖t‖⁻¹ ^ d * M := by sorry
