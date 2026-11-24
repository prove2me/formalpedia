-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_pairI_of_detMono
-- name    : GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:37.269383+00:00
-- url     : https://prove2.me/theorems/0d479c19-afba-4045-96ca-28228f266bfa
-- title:
--   Wedge: pair I of det Mono
-- statement:
--   The Wedge construction uses the pair I of det Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PairingBoundInfinitePlaces.lean#L10-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PairingBoundInfinitePlaces.lean#L10-L76

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundInfinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
open ComplexOrder

theorem GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono : DetMono → PairI := by sorry
