-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_fromCols_of_id
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_fromCols_of_id
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:20.611796+00:00
-- url     : https://prove2.me/theorems/c3a93e61-2716-4f8c-8c45-e4d7d2f3e5e4
-- title:
--   Wedge: n F from Cols of id
-- statement:
--   The Wedge construction uses the n F from Cols of id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L137-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L137-L176

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

theorem GlobalTheory.CompanionTheory.Wedge.nF_fromCols_of_id (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (D : Matrix ι κ K) (C : Matrix ι κ' K)
    (s : κ → ι) (hD : D.submatrix s id = 1) (hint : ∀ i j, ‖D i j‖ ≤ 1)
    (hC : C.submatrix s id = 0) : nF (fromCols D C) = nF C := by sorry
