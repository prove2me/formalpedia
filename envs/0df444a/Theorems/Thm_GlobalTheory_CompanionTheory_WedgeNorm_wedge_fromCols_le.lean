-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeNorm_wedge_fromCols_le
-- name    : GlobalTheory.CompanionTheory.WedgeNorm.wedge_fromCols_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:20.386633+00:00
-- url     : https://prove2.me/theorems/87f9352d-225e-496c-a156-3d1646e5f446
-- title:
--   Wedge Norm: wedge from Cols le
-- statement:
--   The Wedge Norm construction uses the wedge from Cols le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeSubspaceBound.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeSubspaceBound.lean#L8-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeSubspaceBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeNorm

theorem GlobalTheory.CompanionTheory.WedgeNorm.wedge_fromCols_le {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {N : Fam K ι}
    (h : IsWedge N) (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (X : Matrix ι κ K) (Z : Matrix ι κ' K) :
    N (κ ⊕ κ') (fromCols X Z) ≤ N κ X * N κ' Z := by sorry
