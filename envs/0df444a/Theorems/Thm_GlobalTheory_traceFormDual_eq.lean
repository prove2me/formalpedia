-- Prove2me | Theorems.Thm_GlobalTheory_traceFormDual_eq
-- name    : GlobalTheory.traceFormDual_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:56.939633+00:00
-- url     : https://prove2.me/theorems/092a08e5-017d-4e41-91fe-ead2704ea1b9
-- title:
--   Global Theory: trace Form Dual eq
-- statement:
--   The Global Theory construction uses the trace Form Dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L282-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L282-L314

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

theorem GlobalTheory.traceFormDual_eq {ξ : E} (hξ : ξ ≠ 0) :
    traceFormDual ξ G Λ =
      (((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • hermDual G Λ := by sorry
