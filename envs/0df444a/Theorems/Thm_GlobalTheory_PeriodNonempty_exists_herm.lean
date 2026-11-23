-- Prove2me | Theorems.Thm_GlobalTheory_PeriodNonempty_exists_herm
-- name    : GlobalTheory.PeriodNonempty.exists_herm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:35.296576+00:00
-- url     : https://prove2.me/theorems/e6224703-62e3-44e6-b058-e67b47a140a4
-- title:
--   Period Nonempty: exists herm
-- statement:
--   The Period Nonempty construction uses the exists herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L125-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L125-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section

theorem GlobalTheory.PeriodNonempty.exists_herm {g : ℕ} (B : LinearMap.BilinForm ℝ (Fin g → ℂ)) (halt : ∀ x y, B x y = -B y x)
    (hI : ∀ x y, B (Complex.I • x) (Complex.I • y) = B x y) (hpos : ∀ x, x ≠ 0 → 0 < B (Complex.I • x) x) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm x y).im = B x y := by sorry
