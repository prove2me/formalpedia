-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_exists_weight_lt
-- name    : GlobalTheory.RowSpan.exists_weight_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:33:10.202983+00:00
-- url     : https://prove2.me/theorems/58b892af-71bd-49f7-ba14-a1c84d49cd10
-- title:
--   Row Span: exists weight lt
-- statement:
--   The Row Span construction uses the exists weight lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L203-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L203-L216

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

theorem GlobalTheory.RowSpan.exists_weight_lt (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hf : ∀ ℓ, ∀ m ∈ (f (X ℓ) - X ℓ).support, Finsupp.weight w m < w ℓ) (P : MvPolynomial σ k) :
    ∀ m' ∈ (f P - P).support, ∃ m ∈ P.support, Finsupp.weight w m' < Finsupp.weight w m := by sorry
