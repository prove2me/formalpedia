-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainUnion_remove_right
-- name    : GlobalTheory.CompanionTheory.TyFin.chainUnion_remove_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:10.632731+00:00
-- url     : https://prove2.me/theorems/0a3a64af-11d9-4e8e-8447-010e409d8dbd
-- title:
--   Ty Fin: chain Union remove right
-- statement:
--   The Ty Fin construction uses the chain Union remove right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependence.lean#L19-L27

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

theorem GlobalTheory.CompanionTheory.TyFin.chainUnion_remove_right (m k t : ℕ) (q : Fin m) (hq : (q : ℕ) = t + 1) :
    (fun i j => chainUnion m k t i j ∧ ¬ (Sum.isRight i = true ∧ j = Sum.inl q)) =
      chainPat m k (t + 1) := by sorry
