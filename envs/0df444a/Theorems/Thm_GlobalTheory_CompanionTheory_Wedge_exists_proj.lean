-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_exists_proj
-- name    : GlobalTheory.CompanionTheory.Wedge.exists_proj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:17.552809+00:00
-- url     : https://prove2.me/theorems/4c566e31-4aa8-4e5b-be16-9ae82a4b007c
-- title:
--   Wedge: exists proj
-- statement:
--   The Wedge construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L55-L63

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem GlobalTheory.CompanionTheory.Wedge.exists_proj (B : Matrix ι κ ℂ) (hB : LinearIndependent ℂ Bᵀ) :
    ∃ Y : Matrix κ ι ℂ, Y * B = 1 ∧ (B * Y)ᴴ = B * Y := by sorry
