-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaConstantWeber_halfPeriods_notMem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:51.923877+00:00
-- url     : https://prove2.me/theorems/a91b0c5b-7097-4621-baa7-8eba3960684f
-- title:
--   Theta Constant Weber: half Periods not Mem
-- statement:
--   The Theta Constant Weber construction uses the half Periods not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/ThetaConstantWeber.lean#L53-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/ThetaConstantWeber.lean#L53-L76

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem (τ : ℍ) :
    (1 / 2 : ℂ) ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice ∧
      (τ : ℂ) / 2 ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice ∧
      (1 + (τ : ℂ)) / 2 ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice := by sorry
