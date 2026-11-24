-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_card_pairs
-- name    : GlobalTheory.CompanionTheory.RootExch.card_pairs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:55.562777+00:00
-- url     : https://prove2.me/theorems/f2b7fdd6-4d00-48b2-8494-86d2e8d29b0d
-- title:
--   Root Exch: card pairs
-- statement:
--   The Root Exch construction uses the card pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L352-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L352-L396

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch

theorem GlobalTheory.CompanionTheory.RootExch.card_pairs {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (W : ι → Prop) (p q : ι)
    (h1 : ∀ w, W w → Φ p w ∧ Φ w q) :
    Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (W x.1 ∧ x.2 = q)} =
      Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (x.1 = p ∧ W x.2)} := by sorry
