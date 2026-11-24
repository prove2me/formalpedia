-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_harmK_le_of_top
-- name    : GlobalTheory.RowSpan.harmK_le_of_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:16.087478+00:00
-- url     : https://prove2.me/theorems/6efd1daf-188b-4f4a-b24b-ba1d3d41547e
-- title:
--   Row Span: harm K le of top
-- statement:
--   The Row Span construction uses the harm K le of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L447-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L447-L469

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

theorem GlobalTheory.RowSpan.harmK_le_of_top [CharZero k] [Finite T] (cc : T → T) (isX : T → Prop)
    {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (h : ∀ P ∈ harmK r n k cc isX (fun _ => 1), RowInv r n k P → (∃ a : T → ℕ → ℕ, RowDeg r n k a P) → P ∈ U) :
    harmK r n k cc isX (fun _ => 1) ≤ U := by sorry
