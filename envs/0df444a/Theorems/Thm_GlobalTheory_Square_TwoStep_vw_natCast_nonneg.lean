-- Prove2me | Theorems.Thm_GlobalTheory_Square_TwoStep_vw_natCast_nonneg
-- name    : GlobalTheory.Square.TwoStep.vw_natCast_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:01.735816+00:00
-- url     : https://prove2.me/theorems/7acabbd2-bd05-4c18-b284-e0ec4e60fdad
-- title:
--   Two Step: vw nat Cast nonneg
-- statement:
--   The Two Step construction uses the vw nat Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L229-L231

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep

theorem GlobalTheory.Square.TwoStep.vw_natCast_nonneg (w : Pl K) (n : ℕ) : (0 : ℝ) ≤ (vw w (n : K) : ℝ) := by sorry
