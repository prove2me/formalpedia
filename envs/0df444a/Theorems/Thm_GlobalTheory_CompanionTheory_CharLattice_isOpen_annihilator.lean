-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_isOpen_annihilator
-- name    : GlobalTheory.CompanionTheory.CharLattice.isOpen_annihilator
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:23.873542+00:00
-- url     : https://prove2.me/theorems/91209b6b-c707-4ead-9235-8091859aa07f
-- title:
--   Char Lattice: is Open annihilator
-- statement:
--   The Char Lattice construction uses the is Open annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean#L18-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean#L18-L41

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

theorem GlobalTheory.CompanionTheory.CharLattice.isOpen_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) (hb : b ≠ 0) :
    IsOpen (annihilator ψ n b : Set (Fin n → k)) := by sorry
