-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Clozel_multiset_eq_map_neg_conj_of_polyEq
-- name    : GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:53.259939+00:00
-- url     : https://prove2.me/theorems/8a0a568c-37de-4d68-9766-e309de574371
-- title:
--   Clozel: multiset eq map neg conj of poly Eq
-- statement:
--   The Clozel construction uses the multiset eq map neg conj of poly Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetConjugateNegOfProd.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetConjugateNegOfProd.lean#L18-L42

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetConjugateNegOfProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Clozel

theorem GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq :
    ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n →
      (∀ u : ℂ, (m.map (u + ·)).prod =
        (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) →
      m' = m.map fun z => -(starRingEnd ℂ) z := by sorry
