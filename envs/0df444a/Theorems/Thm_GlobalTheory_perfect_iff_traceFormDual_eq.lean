-- Prove2me | Theorems.Thm_GlobalTheory_perfect_iff_traceFormDual_eq
-- name    : GlobalTheory.perfect_iff_traceFormDual_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:12.395801+00:00
-- url     : https://prove2.me/theorems/5f71d745-e364-4ee3-b749-ab70b4d37c11
-- title:
--   Global Theory: perfect iff trace Form Dual eq
-- statement:
--   The Global Theory construction uses the perfect iff trace Form Dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L390-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L390-L410

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

theorem GlobalTheory.perfect_iff_traceFormDual_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0)
    (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ((∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k) ∧
      ∀ φ : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ G x y) ↔
    traceFormDual ξ G Λ = Λ := by sorry
