-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_mem_harmK_iff
-- name    : GlobalTheory.RowSpan.mem_harmK_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:47.568697+00:00
-- url     : https://prove2.me/theorems/d12f05ca-434a-443b-83ee-33ed6509a65c
-- title:
--   Row Span: mem harm K iff
-- statement:
--   The Row Span construction uses the mem harm K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L50-L56

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

theorem GlobalTheory.RowSpan.mem_harmK_iff (cc : T → T) (isX : T → Prop) (P : MvPolynomial (Letter T r n) k) :
    P ∈ harmK r n k cc isX (fun _ => 1) ↔ ∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))),
      ∑ b : Fin n, pderiv (⟨τ, i, b⟩ : Letter T r n) (pderiv (⟨cc τ, i', b⟩ : Letter T r n) P) = 0 := by sorry
