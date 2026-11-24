-- Prove2me | Theorems.Thm_GlobalTheory_Square_stepRatio_vw_pow
-- name    : GlobalTheory.Square.stepRatio_vw_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:09.459051+00:00
-- url     : https://prove2.me/theorems/eee9e3d3-3a5f-4e50-88de-2b9ee54c97bd
-- title:
--   Square: step Ratio vw pow
-- statement:
--   The Square construction uses the step Ratio vw pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/StepRatioAbsVwProd.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/StepRatioAbsVwProd.lean#L14-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_StepRatioAbsVwProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem GlobalTheory.Square.stepRatio_vw_pow (w : Pl K) {x : K} (hx : x ≠ 0) (c : ℕ) : vw w (x ^ c) = c * vw w x := by sorry
