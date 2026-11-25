-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantSecondFundamentalForm_smooth_extFormAdj
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:59.880826+00:00
-- url     : https://prove2.me/theorems/9b05e97d-ac6e-5b41-a6cc-d16aeaba03fe
-- title:
--   Covariant Second Fundamental Form: smooth ext Form Adj
-- statement:
--   The Covariant Second Fundamental Form construction uses the smooth ext Form Adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean#L139-L142

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
variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj (ξ : V) : MContDiffAt ∞ (fun x => extFormAdj H x ξ) z := by sorry
