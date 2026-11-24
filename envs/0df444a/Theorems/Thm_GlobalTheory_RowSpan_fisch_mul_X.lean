-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_fisch_mul_X
-- name    : GlobalTheory.RowSpan.fisch_mul_X
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:00.478773+00:00
-- url     : https://prove2.me/theorems/b8350d50-d846-4295-920a-fe498460d26a
-- title:
--   Row Span: fisch mul X
-- statement:
--   The Row Span construction uses the fisch mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L93-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L93-L107

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
variable {σ : Type}

theorem GlobalTheory.RowSpan.fisch_mul_X (P Q : MvPolynomial σ ℚ) (v : σ) : fisch (P * X v) Q = fisch P (pderiv v Q) := by sorry
