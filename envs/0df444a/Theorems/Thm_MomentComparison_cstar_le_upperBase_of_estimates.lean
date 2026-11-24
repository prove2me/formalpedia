-- Prove2me | Theorems.Thm_MomentComparison_cstar_le_upperBase_of_estimates
-- name    : MomentComparison.cstar_le_upperBase_of_estimates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:05:45.823478+00:00
-- url     : https://prove2.me/theorems/26a77bb0-db86-4b7e-bf06-0eea136fc29c
-- title:
--   Moment Comparison: cstar le upper Base of estimates
-- statement:
--   The upper bound follows from complex hypercontractivity and scalar polynomial
--   growth for the lens of conjugate exponents.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L222-L242
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L222-L242

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison

theorem MomentComparison.cstar_le_upperBase_of_estimates
    (hHyper : ∀ p : ℝ, 2 < p → ∀ (n : ℕ) (f : Cube n → ℂ) (w : ℂ),
      inLens p w → complexMomentNorm p (complexNoise w f) ≤
        complexMomentNorm (p / (p - 1)) f)
    (hGrowth : ∀ p : ℝ, 2 < p → ∀ (d : ℕ) (P : Polynomial ℂ), P.natDegree ≤ d →
      ∀ M : ℝ, 0 ≤ M → (∀ w, inLens p w → ‖P.eval w‖ ≤ M) →
        ‖P.eval 1‖ ≤ lensFactor p ^ d * M) :
    Cstar ≤ upperBase := by sorry
