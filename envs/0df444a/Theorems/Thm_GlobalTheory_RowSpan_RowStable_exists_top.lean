-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_RowStable_exists_top
-- name    : GlobalTheory.RowSpan.RowStable.exists_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:21.988007+00:00
-- url     : https://prove2.me/theorems/f413c548-f5cb-4bd5-8bdf-0d3a3fdd2fae
-- title:
--   Row Stable: exists top
-- statement:
--   The Row Stable construction uses the exists top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L294-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L294-L349

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

theorem GlobalTheory.RowSpan.RowStable.exists_top [Infinite k] {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (h0 : U ≠ ⊥) : ∃ P ∈ U, P ≠ 0 ∧ RowInv r n k P ∧ ∃ a : T → ℕ → ℕ, RowDeg r n k a P := by sorry
