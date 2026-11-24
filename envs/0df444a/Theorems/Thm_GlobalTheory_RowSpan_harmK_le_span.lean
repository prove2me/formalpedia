-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_harmK_le_span
-- name    : GlobalTheory.RowSpan.harmK_le_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:46.89604+00:00
-- url     : https://prove2.me/theorems/c1a71a3e-dc40-4581-b372-97f79596eb34
-- title:
--   Row Span: harm K le span
-- statement:
--   The Row Span construction uses the harm K le span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L408-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L408-L445

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

theorem GlobalTheory.RowSpan.harmK_le_span [CharZero k] (cc : T → T) (isX : T → Prop) :
    harmK r n k cc isX (fun _ => 1) ≤
      Submodule.span k (map (algebraMap ℚ k) '' (harmK r n ℚ cc isX (fun _ => 1))) := by sorry
