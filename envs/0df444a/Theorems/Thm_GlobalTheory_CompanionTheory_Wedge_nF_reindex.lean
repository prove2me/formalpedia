-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_reindex
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_reindex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:37.052537+00:00
-- url     : https://prove2.me/theorems/924036ca-818c-484c-8a4c-d3d36c1a0c2d
-- title:
--   Wedge: n F reindex
-- statement:
--   The Wedge construction uses the n F reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L207-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L207-L215

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

theorem GlobalTheory.CompanionTheory.Wedge.nF_reindex [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (e : κ' ≃ κ) (A : Matrix ι κ K) : nF (A.submatrix id e) = nF A := by sorry
