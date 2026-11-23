-- Prove2me | Theorems.Thm_GlobalTheory_Square_TwoStep_normAlg_coords
-- name    : GlobalTheory.Square.TwoStep.normAlg_coords
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:43.997961+00:00
-- url     : https://prove2.me/theorems/5f0577b6-595a-4f55-940a-aad975b74e53
-- title:
--   Two Step: norm Alg coords
-- statement:
--   The Two Step construction uses the norm Alg coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L260-L262

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

theorem GlobalTheory.Square.TwoStep.normAlg_coords (t : ℕ) : normAlg (square K).G (coords K t).gam (coords K t).z = (t : K) ^ 2 := by sorry
