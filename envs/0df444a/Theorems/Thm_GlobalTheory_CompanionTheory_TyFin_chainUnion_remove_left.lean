-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainUnion_remove_left
-- name    : GlobalTheory.CompanionTheory.TyFin.chainUnion_remove_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:31.917152+00:00
-- url     : https://prove2.me/theorems/bf0a577e-3a50-42d7-b57b-25921c14ea48
-- title:
--   Ty Fin: chain Union remove left
-- statement:
--   The Ty Fin construction uses the chain Union remove left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean#L29-L37

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

theorem GlobalTheory.CompanionTheory.TyFin.chainUnion_remove_left (m k t : ℕ) (p : Fin m) (hp : (p : ℕ) = t) :
    (fun i j => chainUnion m k t i j ∧ ¬ (i = Sum.inl p ∧ Sum.isRight j = true)) =
      chainPat m k t := by sorry
