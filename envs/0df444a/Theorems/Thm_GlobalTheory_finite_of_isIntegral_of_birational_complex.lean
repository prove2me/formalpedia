-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isIntegral_of_birational_complex
-- name    : GlobalTheory.finite_of_isIntegral_of_birational_complex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:02.764133+00:00
-- url     : https://prove2.me/theorems/91bcfc16-bb67-4a3b-85fa-f823161f617f
-- title:
--   Global Theory: finite of is Integral of birational complex
-- statement:
--   The Global Theory construction uses the finite of is Integral of birational complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FiniteOfIsIntegralOfBirationalOfPresentation.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FiniteOfIsIntegralOfBirationalOfPresentation.lean#L68-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FiniteOfIsIntegralOfBirationalOfPresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.finite_of_isIntegral_of_birational_complex
    (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by sorry
