-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_lineParU_nontrivial
-- name    : GlobalTheory.LGrp.lineParU_nontrivial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:39.440292+00:00
-- url     : https://prove2.me/theorems/a0df52b2-0edc-4a5f-be06-5f606fdb7df9
-- title:
--   LGrp: line Par U nontrivial
-- statement:
--   The LGrp construction uses the line Par U nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1618-L1640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1618-L1640

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
omit σ hσ hc
variable {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem GlobalTheory.LGrp.lineParU_nontrivial (h : IsUnramInv ϖ σ q) (n : ℕ) :
    (lineParU σ h.1 (continuous_of_unramInv h) n).U ≠ ⊥ := by sorry
