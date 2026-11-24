-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_wedgeI_of_detMono_mulI
-- name    : GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:43.87717+00:00
-- url     : https://prove2.me/theorems/22a802e7-5896-4144-beb1-21ea982e6c50
-- title:
--   Wedge: wedge I of det Mono mul I
-- statement:
--   The Wedge construction uses the wedge I of det Mono mul I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L101-L106

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

theorem GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI : DetMono → MulI → WedgeI := by sorry
