-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_le_of_minors
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_le_of_minors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:43.81635+00:00
-- url     : https://prove2.me/theorems/725ee7ac-2289-44e2-a5b2-3474a83df5d0
-- title:
--   Wedge: n F le of minors
-- statement:
--   The Wedge construction uses the n F le of minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L19-L21

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

theorem GlobalTheory.CompanionTheory.Wedge.nF_le_of_minors [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s : κ → ι, ‖(A.submatrix s id).det‖ ≤ c) : nF A ≤ c := by sorry
