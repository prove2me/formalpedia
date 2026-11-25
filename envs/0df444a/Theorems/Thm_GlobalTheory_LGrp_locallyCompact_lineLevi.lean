-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_locallyCompact_lineLevi
-- name    : GlobalTheory.LGrp.locallyCompact_lineLevi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:04.340932+00:00
-- url     : https://prove2.me/theorems/f918c9e9-7069-4cf4-9636-f7c1020ecf4e
-- title:
--   LGrp: locally Compact line Levi
-- statement:
--   The LGrp construction uses the locally Compact line Levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1614-L1616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1614-L1616

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

theorem GlobalTheory.LGrp.locallyCompact_lineLevi (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) [LocallyCompactSpace (GU σ (n + 2))] :
    LocallyCompactSpace (Lˣ × GU σ n) := by sorry
