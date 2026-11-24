-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_wt_cons
-- name    : GlobalTheory.CompanionTheory.SegOrder.wt_cons
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:47.540478+00:00
-- url     : https://prove2.me/theorems/f2c82b1e-223f-4e8d-b587-be7a7122bdfd
-- title:
--   Seg Order: wt cons
-- statement:
--   The Seg Order construction uses the wt cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCommonOrderedForm.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCommonOrderedForm.lean#L37-L39

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCommonOrderedForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SegOrder
variable {T : Type u}

theorem GlobalTheory.CompanionTheory.SegOrder.wt_cons (s : T → T) (a : ASeg T) (L : List (ASeg T)) :
    wt s (a :: L) = wt s L ++ ASeg.dec s a := by sorry
