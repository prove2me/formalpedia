-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_entry_eq_minor
-- name    : GlobalTheory.CompanionTheory.Wedge.entry_eq_minor
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:08.931308+00:00
-- url     : https://prove2.me/theorems/c14485cf-8bdf-426c-b343-181b93b868dd
-- title:
--   Wedge: entry eq minor
-- statement:
--   The Wedge construction uses the entry eq minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L124-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L124-L135

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

theorem GlobalTheory.CompanionTheory.Wedge.entry_eq_minor [Fintype κ] [DecidableEq κ] (D : Matrix ι κ K) (s : κ → ι)
    (hD : D.submatrix s id = 1) (i : ι) (k : κ) :
    D i k = (D.submatrix (Function.update s k i) id).det := by sorry
