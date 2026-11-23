-- Prove2me | Theorems.Thm_GlobalTheory_conjFrac_spanSingleton
-- name    : GlobalTheory.conjFrac_spanSingleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:22.939273+00:00
-- url     : https://prove2.me/theorems/f0fd51a4-24cf-4853-990a-08168cafab21
-- title:
--   Global Theory: conj Frac span Singleton
-- statement:
--   The Global Theory construction uses the conj Frac span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L51-L62

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

theorem GlobalTheory.conjFrac_spanSingleton (x : E) :
    conjFrac (FractionalIdeal.spanSingleton (𝓞 E)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (cc x) := by sorry
