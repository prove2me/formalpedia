-- Prove2me | Theorems.Thm_GlobalTheory_Couple_psi_eq_sum_coupIdx
-- name    : GlobalTheory.Couple.psi_eq_sum_coupIdx
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:37.609929+00:00
-- url     : https://prove2.me/theorems/1a748adc-03d6-56df-bce3-d480ec1f96be
-- title:
--   Couple: psi eq sum coup Idx
-- statement:
--   The Couple construction uses the psi eq sum coup Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PsiEqSumCoupIdx.lean#L10-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PsiEqSumCoupIdx.lean#L10-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PsiEqSumCoupIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
noncomputable section
open GlobalTheory GlobalTheory.Couple

theorem GlobalTheory.Couple.psi_eq_sum_coupIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (T : Chain k s X Z) (A : RepFam k s X) (c₁ c₂ : kˣ) (_ : T.Adapted A (box _ c₁) (box _ c₂)) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (ε : k) (S : Finset ((X (s + 1) → k) ⧸ box (X (s + 1)) c₂)) (_ : T.coupIdx A (box _ c₁) (box _ c₂) ⊆ S), ∀ g ∈ A s 0 rfl, ∀ x₀, (∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y) ∧ ∀ η, GlobalTheory.StepData.hat ψ ν ε (T.Psi g x₀) η = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * GlobalTheory.StepData.hat ψ ν ε (cosetInd (box _ c₂) yb) η := by sorry
