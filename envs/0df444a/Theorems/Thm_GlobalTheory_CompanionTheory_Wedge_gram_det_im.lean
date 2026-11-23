-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_gram_det_im
-- name    : GlobalTheory.CompanionTheory.Wedge.gram_det_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:45.352497+00:00
-- url     : https://prove2.me/theorems/d0aedabd-b1bd-4db6-92d7-0ce55dee2c44
-- title:
--   Wedge: gram det im
-- statement:
--   The Wedge construction uses the gram det im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L16-L17

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

theorem GlobalTheory.CompanionTheory.Wedge.gram_det_im (A : Matrix ι κ ℂ) : (Aᴴ * A).det.im = 0 := by sorry
