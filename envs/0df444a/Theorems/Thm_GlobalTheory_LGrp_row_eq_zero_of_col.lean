-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_row_eq_zero_of_col
-- name    : GlobalTheory.LGrp.row_eq_zero_of_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:45.383105+00:00
-- url     : https://prove2.me/theorems/f30225f9-39ba-4824-aab5-0f2d30b83d04
-- title:
--   LGrp: row eq zero of col
-- statement:
--   The LGrp construction uses the row eq zero of col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1465-L1478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1465-L1478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open Formalism.UG
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
omit hσ hc [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.LGrp.row_eq_zero_of_col (g : GU σ n) (c : Fin n) (h : ∀ i, i ≠ c → g.1.val i c = 0) (j : Fin n) (hj : j ≠ c.rev) :
    g.1.val c.rev j = 0 := by sorry
