-- Prove2me | Theorems.Thm_GlobalTheory_mem_traceFormDual
-- name    : GlobalTheory.mem_traceFormDual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:27.954681+00:00
-- url     : https://prove2.me/theorems/ce84af23-e7f0-4ae0-9e30-454955b2e393
-- title:
--   Global Theory: mem trace Form Dual
-- statement:
--   The Global Theory construction uses the mem trace Form Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L279-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L279-L280

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

theorem GlobalTheory.mem_traceFormDual {ξ : E} {x : Fin r → E} :
    x ∈ traceFormDual ξ G Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k := by sorry
