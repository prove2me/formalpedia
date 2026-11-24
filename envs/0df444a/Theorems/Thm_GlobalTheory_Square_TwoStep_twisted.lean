-- Prove2me | Theorems.Thm_GlobalTheory_Square_TwoStep_twisted
-- name    : GlobalTheory.Square.TwoStep.twisted
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:35.517681+00:00
-- url     : https://prove2.me/theorems/09eff937-6c15-4b41-9c32-fcc93b5803c9
-- title:
--   Two Step: twisted
-- statement:
--   The Two Step construction uses the twisted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L300-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L300-L320

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

theorem GlobalTheory.Square.TwoStep.twisted (σ₀ : K →+* ℂ) (w : Pl K) {n m d Q : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hd : d ≠ 0)
    (hQ : (Q : 𝓞 K) ∉ w.asIdeal) {er : ℝ} (her : (vw w (m : K) : ℝ) ≤ (vw w (d : K) : ℝ) + er) :
    (square K).Twisted σ₀ w (σ₀ ((n ^ 2 * m * Q : ℕ) : K) * (square K).base.c) 1 1 (fun _ => 1) (fun _ => d) (fun _ => 0)
      (fun _ => 0) er (vw w ((2 : ℕ) : K) : ℝ) (univ : Finset Unit) (fun _ => 1) (fun _ => n) := by sorry
