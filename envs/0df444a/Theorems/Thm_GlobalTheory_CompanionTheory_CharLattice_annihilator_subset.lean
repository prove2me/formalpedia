-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_annihilator_subset
-- name    : GlobalTheory.CompanionTheory.CharLattice.annihilator_subset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:24.801188+00:00
-- url     : https://prove2.me/theorems/46580b4a-fd8a-47a2-bd44-11f1fc136c1a
-- title:
--   Char Lattice: annihilator subset
-- statement:
--   The Char Lattice construction uses the annihilator subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean#L55-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean#L55-L82

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

theorem GlobalTheory.CompanionTheory.CharLattice.annihilator_subset (ψ : AddChar k Circle) (n : ℕ) (b : k) (hb : b ≠ 0) (y₀ : k)
    (hy : ψ y₀ ≠ 1) :
    (annihilator ψ n b : Set (Fin n → k)) ⊆
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (y₀ / b)}) := by sorry
