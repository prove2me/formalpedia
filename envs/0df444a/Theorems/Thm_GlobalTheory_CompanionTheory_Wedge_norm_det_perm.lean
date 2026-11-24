-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_norm_det_perm
-- name    : GlobalTheory.CompanionTheory.Wedge.norm_det_perm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:43.325902+00:00
-- url     : https://prove2.me/theorems/d26502a3-0b85-4675-aaea-0290a5b37932
-- title:
--   Wedge: norm det perm
-- statement:
--   The Wedge construction uses the norm det perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L72-L75

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]

theorem GlobalTheory.CompanionTheory.Wedge.norm_det_perm [Fintype κ] [DecidableEq κ] (M : Matrix κ κ K) (e : Equiv.Perm κ) :
    ‖(M.submatrix e id).det‖ = ‖M.det‖ := by sorry
