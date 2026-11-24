-- Prove2me | Theorems.Thm_GlobalTheory_Square_AwayClosure_of_pow_eq_one
-- name    : GlobalTheory.Square.AwayClosure.of_pow_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:25:56.49541+00:00
-- url     : https://prove2.me/theorems/8e58cda0-478f-4f89-bebe-daf9194d60c1
-- title:
--   Away Closure: of pow eq one
-- statement:
--   The Away Closure construction uses the of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulPowIntegral.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulPowIntegral.lean#L33-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulPowIntegral
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
noncomputable section
open GlobalTheory GlobalTheory.Square GlobalTheory.Square.AwayClosure
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain Finset
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Square.AwayClosure.of_pow_eq_one (m : ℕ) {x : K} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) :
    _root_.GlobalTheory.Square.IsAwayUnit m x := by sorry
