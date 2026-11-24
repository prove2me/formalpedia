-- Prove2me | Theorems.Thm_GlobalTheory_Square_Ratio_away
-- name    : GlobalTheory.Square.Ratio.away
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:36.160074+00:00
-- url     : https://prove2.me/theorems/bfced3d3-f35e-4520-ab69-6151290fa15d
-- title:
--   Ratio: away
-- statement:
--   The Ratio construction uses the away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRatios.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRatios.lean#L16-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRatios
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul

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
open GlobalTheory GlobalTheory.Square GlobalTheory.Square.Ratio
open Formalism.DivisionValues.ValuationRepresentative (vw_mul vw_inv)

theorem GlobalTheory.Square.Ratio.away {K : Type} [Field K] [NumberField K] [StarRing K] {w : Pl K} {Qn : ℕ}
    (hQ : (Qn : 𝓞 K) ∉ w.asIdeal) {x : K} (h : IsAwayUnit Qn x) : x ≠ 0 ∧ vw w x = 0 := by sorry
