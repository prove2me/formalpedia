-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinReversal_prod_filter_le_rev
-- name    : GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:27.4522+00:00
-- url     : https://prove2.me/theorems/7285d9df-82f5-4ded-ae72-cbd313db284b
-- title:
--   Fin Reversal: prod filter le rev
-- statement:
--   The Fin Reversal construction uses the prod filter le rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdLeRevEqProdGe.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdLeRevEqProdGe.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdLeRevEqProdGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinReversal

theorem GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by sorry
