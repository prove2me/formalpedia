-- Prove2me | Theorems.Thm_GlobalTheory_fractionalIdeal_mul_smul
-- name    : GlobalTheory.fractionalIdeal_mul_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:34.047039+00:00
-- url     : https://prove2.me/theorems/c147a5e8-6c7c-43c1-b8af-04e8c53b10a5
-- title:
--   Global Theory: fractional Ideal mul smul
-- statement:
--   The Global Theory construction uses the fractional Ideal mul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L103-L108

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

theorem GlobalTheory.fractionalIdeal_mul_smul (a b : FractionalIdeal (𝓞 E)⁰ E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    ((a * b : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ =
      (a : Submodule (𝓞 E) E) • (b : Submodule (𝓞 E) E) • Λ := by sorry
