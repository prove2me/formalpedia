-- Prove2me | Theorems.Thm_GlobalTheory_IrredSB_sep
-- name    : GlobalTheory.IrredSB.sep
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:09.807904+00:00
-- url     : https://prove2.me/theorems/450c8296-b341-432b-923f-cb09915532f4
-- title:
--   Irred SB: sep
-- statement:
--   The Irred SB construction uses the sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L189-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L189-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [Fintype Y']

theorem GlobalTheory.IrredSB.sep [CharZero k] (ψk : AddChar k Circle) (hψ : Continuous ψk) (h1 : ψk ≠ 1) {n : ℕ} (hn : 0 < n)
    (p : Matrix Y Y' k) (hp : p ∉ lat k Y Y' n) :
    ∃ b, (∀ u ∈ lat k Y Y' n, (ψk (pair b u) : ℂ) = 1) ∧ (ψk (pair b p) : ℂ) ≠ 1 := by sorry
