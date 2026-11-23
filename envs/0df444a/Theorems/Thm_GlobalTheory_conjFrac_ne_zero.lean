-- Prove2me | Theorems.Thm_GlobalTheory_conjFrac_ne_zero
-- name    : GlobalTheory.conjFrac_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:46.674324+00:00
-- url     : https://prove2.me/theorems/db842b9b-b49e-4ac3-b8a3-2dc8f2ba8c5d
-- title:
--   Global Theory: conj Frac ne zero
-- statement:
--   The Global Theory construction uses the conj Frac ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L45-L46

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

theorem GlobalTheory.conjFrac_ne_zero {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0) : conjFrac a ≠ 0 := by sorry
