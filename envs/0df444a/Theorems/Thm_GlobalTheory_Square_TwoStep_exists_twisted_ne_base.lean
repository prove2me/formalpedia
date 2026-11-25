-- Prove2me | Theorems.Thm_GlobalTheory_Square_TwoStep_exists_twisted_ne_base
-- name    : GlobalTheory.Square.TwoStep.exists_twisted_ne_base
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:25:54.092403+00:00
-- url     : https://prove2.me/theorems/618dc177-4bce-5348-9c50-209ce80dd4e1
-- title:
--   Two Step: exists twisted ne base
-- statement:
--   The Two Step construction uses the exists twisted ne base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L322-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L322-L333

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

theorem GlobalTheory.Square.TwoStep.exists_twisted_ne_base (σ₀ : K →+* ℂ) (w : Pl K) :
    ∃ (S : Sq K) (cw : ℂ) (dl : ℝ), S.OK 3 2 ∧ 0 ≤ dl ∧ cw = 12 * S.base.c ∧ cw ≠ S.base.c ∧
      S.Twisted σ₀ w cw 1 1 (fun _ => 1) (fun _ => 3) (fun _ => 0) (fun _ => 0) 0 dl (univ : Finset Unit) (fun _ => 1)
        (fun _ => 2) := by sorry
