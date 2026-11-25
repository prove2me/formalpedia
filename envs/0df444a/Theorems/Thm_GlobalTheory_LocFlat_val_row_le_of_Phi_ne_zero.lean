-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_val_row_le_of_Phi_ne_zero
-- name    : GlobalTheory.LocFlat.val_row_le_of_Phi_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:11:59.800422+00:00
-- url     : https://prove2.me/theorems/2144811b-87b6-4a41-a3af-15d0c3e76ecc
-- title:
--   Loc Flat: val row le of Phi ne zero
-- statement:
--   The Loc Flat construction uses the val row le of Phi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapRowEqZeroUnlessRowMemDualLattice.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapRowEqZeroUnlessRowMemDualLattice.lean#L9-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLattice
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
open GlobalTheory GlobalTheory.LocFlat

theorem GlobalTheory.LocFlat.val_row_le_of_Phi_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + 1 + c = s) (r : ℕ)
    (hc : c = 2 * r) (w : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hw : (S.T t).Phi j (c + 1) (by omega) w ≠ 0) (y : XIx (Fin κ) t j) :
    valuation k (w (Sum.inr ⟨r, by omega⟩) (Sum.inl y)) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by sorry
