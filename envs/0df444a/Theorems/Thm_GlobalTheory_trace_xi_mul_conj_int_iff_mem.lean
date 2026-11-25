-- Prove2me | Theorems.Thm_GlobalTheory_trace_xi_mul_conj_int_iff_mem
-- name    : GlobalTheory.trace_xi_mul_conj_int_iff_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:12:33.687275+00:00
-- url     : https://prove2.me/theorems/f5d6b394-eb60-463c-915b-5f408be1ab35
-- title:
--   Global Theory: trace xi mul conj int iff mem
-- statement:
--   The Global Theory construction uses the trace xi mul conj int iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/TraceMulConjIntIffMemOfMulDifferentEqOne.lean#L35-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/TraceMulConjIntIffMemOfMulDifferentEqOne.lean#L35-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_TraceMulConjIntIffMemOfMulDifferentEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open GlobalTheory
open NumberField
open scoped Matrix

theorem GlobalTheory.trace_xi_mul_conj_int_iff_mem :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 0 < r → 𝔄 ≠ 0 → X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u} → ∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y) = n) ↔ x ∈ 𝔄 := by sorry
