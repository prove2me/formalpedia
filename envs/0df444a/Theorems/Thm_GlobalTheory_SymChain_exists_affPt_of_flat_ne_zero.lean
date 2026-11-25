-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_exists_affPt_of_flat_ne_zero
-- name    : GlobalTheory.SymChain.exists_affPt_of_flat_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:07.972602+00:00
-- url     : https://prove2.me/theorems/2405600c-f104-51c3-b63d-0836b99dd7dc
-- title:
--   Sym Chain: exists aff Pt of flat ne zero
-- statement:
--   The Sym Chain construction uses the exists aff Pt of flat ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/OneIndexOfOneClassOfSupportOne.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/OneIndexOfOneClassOfSupportOne.lean#L10-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_OneIndexOfOneClassOfSupportOne
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
open GlobalTheory GlobalTheory.SymChain

theorem GlobalTheory.SymChain.exists_affPt_of_flat_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) (h0 : flat ψ ν μ Φ 1 h ≠ 0) :
    ∃ x₀ e, Φ ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 := by sorry
