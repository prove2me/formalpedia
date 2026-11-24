-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_mul_right
-- name    : GlobalTheory.CompanionTheory.WedgeMinor.nF_mul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:16.925794+00:00
-- url     : https://prove2.me/theorems/14d5e737-cb13-4adc-a63a-fa03bafb4a39
-- title:
--   Wedge Minor: n F mul right
-- statement:
--   The Wedge Minor construction uses the n F mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L54-L62

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

theorem GlobalTheory.CompanionTheory.WedgeMinor.nF_mul_right {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by sorry
