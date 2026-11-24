-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_weight_lt_mul
-- name    : GlobalTheory.RowSpan.weight_lt_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:43.209543+00:00
-- url     : https://prove2.me/theorems/d6245f20-1e2c-4e78-9260-cb4b3b15443a
-- title:
--   Row Span: weight lt mul
-- statement:
--   The Row Span construction uses the weight lt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L148-L156

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

theorem GlobalTheory.RowSpan.weight_lt_mul {p q : MvPolynomial σ k} {a b : ℕ} (hp : ∀ m ∈ p.support, Finsupp.weight w m < a)
    (hq : ∀ m ∈ q.support, Finsupp.weight w m ≤ b) : ∀ m ∈ (p * q).support, Finsupp.weight w m < a + b := by sorry
