-- Prove2me | Theorems.Thm_GlobalTheory_fractionalIdeal_smul_inv_smul
-- name    : GlobalTheory.fractionalIdeal_smul_inv_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:19.31521+00:00
-- url     : https://prove2.me/theorems/2b8422ff-ccc0-4e1c-b955-a3b74803f9fd
-- title:
--   Global Theory: fractional Ideal smul inv smul
-- statement:
--   The Global Theory construction uses the fractional Ideal smul inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L117-L120

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

theorem GlobalTheory.fractionalIdeal_smul_inv_smul {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • ((a⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ = Λ := by sorry
