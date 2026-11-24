-- Prove2me | Theorems.Thm_GlobalTheory_Square_AwayClosure_of_integral
-- name    : GlobalTheory.Square.AwayClosure.of_integral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:07:54.769994+00:00
-- url     : https://prove2.me/theorems/d0c16ed7-28de-4286-936d-0432dfb14bb0
-- title:
--   Away Closure: of integral
-- statement:
--   The Away Closure construction uses the of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulPowIntegral.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulPowIntegral.lean#L22-L28

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

theorem GlobalTheory.Square.AwayClosure.of_integral {m k l : ℕ} {x : K} (hx : x ≠ 0) {a b : 𝓞 K}
    (ha : x * (m : K) ^ k = a) (hb : x⁻¹ * (m : K) ^ l = b) : _root_.GlobalTheory.Square.IsAwayUnit m x := by sorry
