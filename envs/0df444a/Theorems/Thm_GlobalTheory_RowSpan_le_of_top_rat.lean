-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_le_of_top_rat
-- name    : GlobalTheory.RowSpan.le_of_top_rat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:42.552774+00:00
-- url     : https://prove2.me/theorems/1552bf02-c836-4242-8760-ac61e8cbc9a0
-- title:
--   Row Span: le of top rat
-- statement:
--   The Row Span construction uses the le of top rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L354-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L354-L382

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

theorem GlobalTheory.RowSpan.le_of_top_rat [Finite T] {U V : Submodule ℚ (MvPolynomial (Letter T r n) ℚ)} (hU : RowStable U)
    (hV : RowStable V) (h : ∀ P ∈ V, RowInv r n ℚ P → (∃ a : T → ℕ → ℕ, RowDeg r n ℚ a P) → P ∈ U) : V ≤ U := by sorry
