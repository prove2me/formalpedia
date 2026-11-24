-- Prove2me | Theorems.Thm_GlobalTheory_hermDual_eq_self_iff
-- name    : GlobalTheory.hermDual_eq_self_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:52.245779+00:00
-- url     : https://prove2.me/theorems/25401dac-6c01-4c64-b6f1-7600e5b0869e
-- title:
--   Global Theory: herm Dual eq self iff
-- statement:
--   The Global Theory construction uses the herm Dual eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L428-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L428-L431

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}

theorem GlobalTheory.hermDual_eq_self_iff :
    hermDual G Λ = Λ ↔ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → x ∈ Λ := by sorry
