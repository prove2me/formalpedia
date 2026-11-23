-- Prove2me | Theorems.Thm_GlobalTheory_fractionalIdeal_one_smul
-- name    : GlobalTheory.fractionalIdeal_one_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:12.317216+00:00
-- url     : https://prove2.me/theorems/42e49200-02da-4a47-b8f8-214d90a6e535
-- title:
--   Global Theory: fractional Ideal one smul
-- statement:
--   The Global Theory construction uses the fractional Ideal one smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L111-L114

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
omit [IsCMField E]

theorem GlobalTheory.fractionalIdeal_one_smul (Λ : Submodule (𝓞 E) (Fin r → E)) :
    ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ = Λ := by sorry
