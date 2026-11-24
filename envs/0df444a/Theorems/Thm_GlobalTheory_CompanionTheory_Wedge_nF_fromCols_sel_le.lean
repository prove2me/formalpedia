-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_fromCols_sel_le
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_fromCols_sel_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:29.327477+00:00
-- url     : https://prove2.me/theorems/bd6e612a-9a10-4d11-bd67-845127a8068a
-- title:
--   Wedge: n F from Cols sel le
-- statement:
--   The Wedge construction uses the n F from Cols sel le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L77-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L77-L122

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

theorem GlobalTheory.CompanionTheory.Wedge.nF_fromCols_sel_le [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (s : κ → ι) (C : Matrix ι κ' K)
    (hs : Function.Injective s) (hC : C.submatrix s id = 0) :
    nF (fromCols ((1 : Matrix ι ι K).submatrix s id)ᵀ C) ≤ nF C := by sorry
