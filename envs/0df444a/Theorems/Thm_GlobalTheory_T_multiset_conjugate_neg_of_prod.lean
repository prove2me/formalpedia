-- Prove2me | Theorems.Thm_GlobalTheory_T_multiset_conjugate_neg_of_prod
-- name    : GlobalTheory.T.multiset_conjugate_neg_of_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:44.328551+00:00
-- url     : https://prove2.me/theorems/43945d2b-b8e4-5934-a9c2-63f95d8ab1bd
-- title:
--   T: multiset conjugate neg of prod
-- statement:
--   The T construction uses the multiset conjugate neg of prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetConjugateNegOfProdStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetConjugateNegOfProdStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetConjugateNegOfProd
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetConjugateNegOfProdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.multiset_conjugate_neg_of_prod : ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n → (∀ u : ℂ, (m.map (u + ·)).prod = (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) → m' = m.map fun z => -(starRingEnd ℂ) z := by sorry
