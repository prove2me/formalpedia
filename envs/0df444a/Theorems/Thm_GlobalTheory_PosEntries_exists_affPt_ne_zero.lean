-- Prove2me | Theorems.Thm_GlobalTheory_PosEntries_exists_affPt_ne_zero
-- name    : GlobalTheory.PosEntries.exists_affPt_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:17.588808+00:00
-- url     : https://prove2.me/theorems/868e9bed-43d3-4fcc-a83d-8a78f7eb98e4
-- title:
--   Pos Entries: exists aff Pt ne zero
-- statement:
--   The Pos Entries construction uses the exists aff Pt ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L77-L83

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
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.PosEntries.exists_affPt_ne_zero (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : opE ψ ν p Ψ x₀ ≠ 0) :
    ∃ e, Ψ (affPt p x₀ e) ≠ 0 := by sorry
