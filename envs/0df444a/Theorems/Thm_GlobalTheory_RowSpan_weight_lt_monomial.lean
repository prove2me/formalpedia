-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_weight_lt_monomial
-- name    : GlobalTheory.RowSpan.weight_lt_monomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:46.540282+00:00
-- url     : https://prove2.me/theorems/4248753f-3c7f-43d7-8011-39d70eedb126
-- title:
--   Row Span: weight lt monomial
-- statement:
--   The Row Span construction uses the weight lt monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L158-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L158-L201

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
variable {σ : Type} (w : σ → ℕ)

theorem GlobalTheory.RowSpan.weight_lt_monomial (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hf : ∀ ℓ, ∀ m ∈ (f (X ℓ) - X ℓ).support, Finsupp.weight w m < w ℓ) (m : σ →₀ ℕ) :
    ∀ m' ∈ (f (monomial m 1) - monomial m 1).support, Finsupp.weight w m' < Finsupp.weight w m := by sorry
