-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeNorm_wedgeSub
-- name    : GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:22.942822+00:00
-- url     : https://prove2.me/theorems/09661347-6ec3-4ace-b87a-5ccc5f1d534a
-- title:
--   Wedge Norm: wedge Sub
-- statement:
--   The Wedge Norm construction uses the wedge Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeSubspaceBound.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeSubspaceBound.lean#L29-L47

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

theorem GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub : WedgeSub := by sorry
