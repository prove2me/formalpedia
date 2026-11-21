-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_shared_pool_decoder_coherent_copy
-- name    : InfoLossLAR.WorstCase.RegevSearch.shared_pool_decoder_coherent_copy
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:33:25.910503+00:00
-- url     : https://prove2.me/theorems/54bf4665-e820-4ca1-8497-b0a0a99166c2
-- title:
--   Coherent copying of the native decoder answer with one shared Gaussian pool
-- statement:
--   For a fixed polynomial call count, show that the available per-query average failure bound at the public precision controls the mean native quantum state error on every normalized finite superposition of promised queries. The query amplitudes are independent of the one stored Gaussian pool. The machine may have different input lengths on different branches. The signed-answer register is compared with the desired finite answer while retaining every original workspace wire. Prove the stated countable-pool estimate uniformly in the basis, width, accuracy and input, with a single negligible residual.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemma 3.14, for the decoding-to-Gaussian reduction. The native circuit and countable common-pool error statements here are specific to this formalization.

import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch RegevLWE.GaussConv
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem shared_pool_decoder_coherent_copy
    {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ}
    (h : CoherentPoolBDDBudget C P N S) (calls : Polynomial ℕ) :
    ∃ e : ℕ → ℝ, Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
