-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_fisch_rowAct
-- name    : GlobalTheory.RowSpan.fisch_rowAct
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:53.946064+00:00
-- url     : https://prove2.me/theorems/ab07fa60-e53a-4a8a-a6cd-ed925df034c8
-- title:
--   Row Span: fisch row Act
-- statement:
--   The Row Span construction uses the fisch row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L122-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L122-L142

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

theorem GlobalTheory.RowSpan.fisch_rowAct (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) ℚ) (P Q : MvPolynomial (Letter T r n) ℚ) :
    fisch (rowAct g P) Q = fisch P (rowAct (fun σ => (g σ).transpose) Q) := by sorry
