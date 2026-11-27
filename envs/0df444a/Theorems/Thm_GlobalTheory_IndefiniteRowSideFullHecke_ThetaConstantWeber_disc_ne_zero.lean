-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaConstantWeber_disc_ne_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.disc_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:55.040951+00:00
-- url     : https://prove2.me/theorems/dd32e634-2cc0-4ff8-bcde-ca2234fee542
-- title:
--   Theta Constant Weber: disc ne zero
-- statement:
--   The Theta Constant Weber construction uses the disc ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/ThetaConstantWeber.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/ThetaConstantWeber.lean#L31-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real

theorem GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.disc_ne_zero (τ : ℍ) :
    (_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (_root_.GlobalTheory.periodPairOfTau τ).g₃ ^ 2
      ≠ 0 := by sorry
