-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_nonneg
-- name    : GlobalTheory.CompanionTheory.WedgeMinor.nF_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:58.316789+00:00
-- url     : https://prove2.me/theorems/3aa0da0b-0fa9-408e-ab7a-b721481822c2
-- title:
--   Wedge Minor: n F nonneg
-- statement:
--   The Wedge Minor construction uses the n F nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L28-L30

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

theorem GlobalTheory.CompanionTheory.WedgeMinor.nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) : 0 ≤ nF A := by sorry
