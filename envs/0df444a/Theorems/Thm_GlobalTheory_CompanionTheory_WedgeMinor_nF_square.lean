-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_square
-- name    : GlobalTheory.CompanionTheory.WedgeMinor.nF_square
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:17.26955+00:00
-- url     : https://prove2.me/theorems/1def74c9-f672-4aa3-811c-998aea8905a5
-- title:
--   Wedge Minor: n F square
-- statement:
--   The Wedge Minor construction uses the n F square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L64-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L64-L78

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeMinor

theorem GlobalTheory.CompanionTheory.WedgeMinor.nF_square {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by sorry
