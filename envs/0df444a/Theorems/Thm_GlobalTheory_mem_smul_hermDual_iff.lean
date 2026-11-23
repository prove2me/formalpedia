-- Prove2me | Theorems.Thm_GlobalTheory_mem_smul_hermDual_iff
-- name    : GlobalTheory.mem_smul_hermDual_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:25.778798+00:00
-- url     : https://prove2.me/theorems/e20b97a0-4355-4ab0-8d85-f0c42bf7478a
-- title:
--   Global Theory: mem smul herm Dual iff
-- statement:
--   The Global Theory construction uses the mem smul herm Dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L189-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L189-L213

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

theorem GlobalTheory.mem_smul_hermDual_iff {b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) {x : Fin r → E} :
    x ∈ (b : Submodule (𝓞 E) E) • hermDual G Λ ↔ ∀ y ∈ Λ, herm G x y ∈ b := by sorry
