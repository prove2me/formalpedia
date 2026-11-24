-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_rowAct_X
-- name    : GlobalTheory.RowSpan.rowAct_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:05.041852+00:00
-- url     : https://prove2.me/theorems/85fc3d5a-7f3e-476e-b122-1721bdbd1ec6
-- title:
--   Row Span: row Act X
-- statement:
--   The Row Span construction uses the row Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L19-L20

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

theorem GlobalTheory.RowSpan.rowAct_X (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) (ℓ : Letter T r n) :
    rowAct g (X ℓ) = ∑ j, C (g ℓ.1 ℓ.2.1 j) * X ⟨ℓ.1, j, ℓ.2.2⟩ := by sorry
