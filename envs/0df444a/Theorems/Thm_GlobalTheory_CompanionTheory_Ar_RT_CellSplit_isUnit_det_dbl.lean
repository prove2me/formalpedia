-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_isUnit_det_dbl
-- name    : GlobalTheory.CompanionTheory.Ar.RT.CellSplit.isUnit_det_dbl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:58.921795+00:00
-- url     : https://prove2.me/theorems/b5122c46-e748-41ee-adbf-79f780505c6e
-- title:
--   Cell Split: is Unit det dbl
-- statement:
--   The Cell Split construction uses the is Unit det dbl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L151-L154

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM

theorem GlobalTheory.CompanionTheory.Ar.RT.CellSplit.isUnit_det_dbl {E β : Type} [CommRing E] [Fintype β] [DecidableEq β] (J : Matrix β β E) (h : IsUnit J.det) :
    IsUnit (dbl J).det := by sorry
