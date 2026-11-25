-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantSecondFundamentalForm_isUnit_sub
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:59.386255+00:00
-- url     : https://prove2.me/theorems/d0e5839c-9ccf-4bba-b6f5-c657f6528ac7
-- title:
--   Covariant Second Fundamental Form: is Unit sub
-- statement:
--   The Covariant Second Fundamental Form construction uses the is Unit sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean#L100-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]
variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub (h : IsPosFrame U H) (z : V) (hz : z ∈ U) : IsUnit (subGram (H z)).det := by sorry
