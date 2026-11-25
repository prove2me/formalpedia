-- Prove2me | Theorems.Thm_GlobalTheory_PosEntries_entries_core
-- name    : GlobalTheory.PosEntries.entries_core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:01.315938+00:00
-- url     : https://prove2.me/theorems/e25cead7-fa5a-4f16-844a-8ce1f677a55f
-- title:
--   Pos Entries: entries core
-- statement:
--   The Pos Entries construction uses the entries core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L91-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L91-L216

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.PosEntries.entries_core (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : HasConductor ψ 1)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c p : ℕ) (hp1 : 1 ≤ p) (A : GL (n ⊕ Fin c) k)
    (hA1 : A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hA2 : A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (hB1 : (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hB2 : (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hInt : ∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val))
    (hMax : ∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) →
      Ψ (x + z) = Ψ x)
    (hE : opE ψ ν p Ψ ≠ 0) :
    (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧
      (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧
    ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by sorry
