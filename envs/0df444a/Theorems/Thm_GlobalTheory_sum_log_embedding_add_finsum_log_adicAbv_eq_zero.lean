-- Prove2me | Theorems.Thm_GlobalTheory_sum_log_embedding_add_finsum_log_adicAbv_eq_zero
-- name    : GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:45.732861+00:00
-- url     : https://prove2.me/theorems/06b112a6-7584-5e30-8864-3ae7784632fd
-- title:
--   Global Theory: sum log embedding add finsum log adic Abv eq zero
-- statement:
--   The Global Theory construction uses the sum log embedding add finsum log adic Abv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumLogEmbeddingAddFinsumLogAdicAbvEqZero.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumLogEmbeddingAddFinsumLogAdicAbvEqZero.lean#L7-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SumLogEmbeddingAddFinsumLogAdicAbvEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero
    (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite ∧
      (∑ σ : F →+* ℂ, Real.log ‖σ N‖) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 F),
          Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = 0 := by sorry
