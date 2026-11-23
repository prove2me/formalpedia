-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_exists_minor_eq_nF
-- name    : GlobalTheory.CompanionTheory.Wedge.exists_minor_eq_nF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:49.404573+00:00
-- url     : https://prove2.me/theorems/07cd28a8-5fdf-4c7f-ab64-a937fe170e04
-- title:
--   Wedge: exists minor eq n F
-- statement:
--   The Wedge construction uses the exists minor eq n F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L23-L29

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

theorem GlobalTheory.CompanionTheory.Wedge.exists_minor_eq_nF [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K)
    (h : nF A ≠ 0) : ∃ s : κ → ι, ‖(A.submatrix s id).det‖ = nF A := by sorry
