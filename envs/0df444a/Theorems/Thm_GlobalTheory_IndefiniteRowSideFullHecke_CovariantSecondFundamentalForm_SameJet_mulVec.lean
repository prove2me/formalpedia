-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantSecondFundamentalForm_SameJet_mulVec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.SameJet.mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:47.525917+00:00
-- url     : https://prove2.me/theorems/461fb04b-aac6-4ee0-8983-5b24bab36149
-- title:
--   Same Jet: mul Vec
-- statement:
--   The Same Jet construction uses the mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean#L40-L47

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
variable {k : Type*} {u u' v v' : V → k → ℂ} {z : V}
omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.SameJet.mulVec [Fintype k] {p : Type*} {M : V → Matrix p k ℂ} (hM : MContDiffAt 1 M z)
    (h : SameJet u u' z) : SameJet (fun x => M x *ᵥ u x) (fun x => M x *ᵥ u' x) z := by sorry
