-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_pderiv_rowAct
-- name    : GlobalTheory.RowSpan.pderiv_rowAct
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:53.209806+00:00
-- url     : https://prove2.me/theorems/30a70545-df4e-496c-a506-6fb59b82b9a2
-- title:
--   Row Span: pderiv row Act
-- statement:
--   The Row Span construction uses the pderiv row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L25-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L25-L48

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

theorem GlobalTheory.RowSpan.pderiv_rowAct (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) (σ : T) (j : Fin (r σ)) (b : Fin n)
    (Q : MvPolynomial (Letter T r n) k) :
    pderiv (⟨σ, j, b⟩ : Letter T r n) (rowAct g Q) =
      ∑ i, g σ i j • rowAct g (pderiv (⟨σ, i, b⟩ : Letter T r n) Q) := by sorry
