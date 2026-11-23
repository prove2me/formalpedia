-- Prove2me | Theorems.Thm_GlobalTheory_Square_Sq_Twisted_ne_zero
-- name    : GlobalTheory.Square.Sq.Twisted.ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:39.532149+00:00
-- url     : https://prove2.me/theorems/f0890418-c8ce-43cf-a2f1-0f93874c5327
-- title:
--   Twisted: ne zero
-- statement:
--   The Twisted construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L221-L225

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

theorem GlobalTheory.Square.Sq.Twisted.ne_zero {S : Sq K} {hd y : ℕ} {σ₀ : K →+* ℂ} {w : Pl K} {cw : ℂ} {zA zA' : K}
    {zT zTd : ℤ → K} {gT : ℤ → ℤ} {n0 : ℤ → ℝ} {er dl : ℝ} {T : Type} {S0 : Finset T} {cc qq : T → ℕ}
    (h : S.Twisted σ₀ w cw zA zA' zT zTd gT n0 er dl S0 cc qq) (hS : S.OK hd y) : cw ≠ 0 := by sorry
