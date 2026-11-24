-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nI_ne_zero_iff_det
-- name    : GlobalTheory.CompanionTheory.Wedge.nI_ne_zero_iff_det
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:30.090992+00:00
-- url     : https://prove2.me/theorems/b2141671-4e5d-4538-9f02-21282b644138
-- title:
--   Wedge: n I ne zero iff det
-- statement:
--   The Wedge construction uses the n I ne zero iff det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L22-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
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
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem GlobalTheory.CompanionTheory.Wedge.nI_ne_zero_iff_det (A : Matrix ι κ ℂ) : nI A ≠ 0 ↔ (Aᴴ * A).det ≠ 0 := by sorry
