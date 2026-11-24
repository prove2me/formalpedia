-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainUnion_isPat
-- name    : GlobalTheory.CompanionTheory.TyFin.chainUnion_isPat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:47.176473+00:00
-- url     : https://prove2.me/theorems/28e342a9-9c0c-44a2-abab-086022d4a4bd
-- title:
--   Ty Fin: chain Union is Pat
-- statement:
--   The Ty Fin construction uses the chain Union is Pat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.chainUnion_isPat (m k t : ℕ) : IsPat (chainUnion m k t) := by sorry
