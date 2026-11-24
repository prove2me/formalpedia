-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_isClosed_annihilator
-- name    : GlobalTheory.CompanionTheory.CharLattice.isClosed_annihilator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:07.804454+00:00
-- url     : https://prove2.me/theorems/42fcd91f-1c60-465a-bbe0-3e5f59ea8a9a
-- title:
--   Char Lattice: is Closed annihilator
-- statement:
--   The Char Lattice construction uses the is Closed annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean#L43-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharLattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.CharLattice.isClosed_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) :
    IsClosed (annihilator ψ n b : Set (Fin n → k)) := by sorry
