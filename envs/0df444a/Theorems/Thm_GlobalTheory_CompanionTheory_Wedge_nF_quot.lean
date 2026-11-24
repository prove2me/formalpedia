-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_quot
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_quot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:43.330618+00:00
-- url     : https://prove2.me/theorems/cb5f60a5-1f0b-4d4e-bf11-626b38080209
-- title:
--   Wedge: n F quot
-- statement:
--   The Wedge construction uses the n F quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L217-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L217-L266

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

theorem GlobalTheory.CompanionTheory.Wedge.nF_quot (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (B : Matrix ι κ K) (hB : LinearIndependent K Bᵀ) :
    ∃ Y : Matrix κ ι K, ∀ (κ' : Type) [Fintype κ'] [DecidableEq κ'] (C : Matrix ι κ' K),
      nF (fromCols B C) = nF B * nF ((1 - B * Y) * C) ∧ nF ((1 - B * Y) * C) ≤ nF C ∧
        (1 - B * Y) * B = 0 := by sorry
