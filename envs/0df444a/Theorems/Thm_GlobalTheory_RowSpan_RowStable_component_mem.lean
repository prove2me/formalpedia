-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_RowStable_component_mem
-- name    : GlobalTheory.RowSpan.RowStable.component_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:54.860699+00:00
-- url     : https://prove2.me/theorems/ca1ad9ed-ef04-4df8-8f9c-9cb5257041bf
-- title:
--   Row Stable: component mem
-- statement:
--   The Row Stable construction uses the component mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L249-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L249-L292

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

theorem GlobalTheory.RowSpan.RowStable.component_mem [Infinite k] {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ U) (a : (Σ σ, Fin (r σ)) →₀ ℕ) :
    weightedHomogeneousComponent (fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1) a P ∈ U := by sorry
