-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_ne_zero_iff
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_ne_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:48.1368+00:00
-- url     : https://prove2.me/theorems/598d15a6-8b97-46d5-93f2-4d212df5eb08
-- title:
--   Wedge: n F ne zero iff
-- statement:
--   The Wedge construction uses the n F ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L178-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L178-L205

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

theorem GlobalTheory.CompanionTheory.Wedge.nF_ne_zero_iff (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≠ 0 ↔ LinearIndependent K Aᵀ := by sorry
