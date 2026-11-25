-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_borelU_two_nontrivial
-- name    : GlobalTheory.LGrp.borelU_two_nontrivial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:13.475172+00:00
-- url     : https://prove2.me/theorems/49ba93e8-fc47-44f4-b7a7-cc62a14b71cf
-- title:
--   LGrp: borel U two nontrivial
-- statement:
--   The LGrp construction uses the borel U two nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1014-L1031
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1014-L1031

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
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.LGrp.borelU_two_nontrivial {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : (borelU σ 2).U ≠ ⊥ := by sorry
