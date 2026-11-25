-- Prove2me | Theorems.Thm_GlobalTheory_exists_mvPolynomial_of_poly_bound_off_hypersurface
-- name    : GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:15.474078+00:00
-- url     : https://prove2.me/theorems/b403a7a6-4650-4eab-937e-c3f47288b7f2
-- title:
--   Global Theory: exists mv Polynomial of poly bound off hypersurface
-- statement:
--   The Global Theory construction uses the exists mv Polynomial of poly bound off hypersurface property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMvPolynomialOfPolyBoundOffHypersurface.lean#L155-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMvPolynomialOfPolyBoundOffHypersurface.lean#L155-L316

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMvPolynomialOfPolyBoundOffHypersurface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
open GlobalTheory
open Filter Topology Asymptotics

theorem GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface :
    ∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        f x = MvPolynomial.eval x p := by sorry
