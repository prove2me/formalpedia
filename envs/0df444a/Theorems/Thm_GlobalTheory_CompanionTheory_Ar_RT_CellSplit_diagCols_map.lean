-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_diagCols_map
-- name    : GlobalTheory.CompanionTheory.Ar.RT.CellSplit.diagCols_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:34.645838+00:00
-- url     : https://prove2.me/theorems/5b274a86-5ba7-4f85-bf88-4dc74aee97c9
-- title:
--   Cell Split: diag Cols map
-- statement:
--   The Cell Split construction uses the diag Cols map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L78-L89

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

theorem GlobalTheory.CompanionTheory.Ar.RT.CellSplit.diagCols_map {S T β : Type} [CommRing S] [CommRing T] [DecidableEq β] (f : S →+* T) :
    (diagCols β : Matrix (β ⊕ β) β S).map f = diagCols β := by sorry
