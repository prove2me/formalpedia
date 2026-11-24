-- Prove2me | Theorems.Thm_GlobalTheory_perfect_iff_hermDual_eq
-- name    : GlobalTheory.perfect_iff_hermDual_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:26:43.153867+00:00
-- url     : https://prove2.me/theorems/d2378026-969b-4eb0-834a-09e361533837
-- title:
--   Global Theory: perfect iff herm Dual eq
-- statement:
--   The Global Theory construction uses the perfect iff herm Dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L412-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L412-L426

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

theorem GlobalTheory.perfect_iff_hermDual_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0)
    (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ((∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k) ∧
      ∀ φ : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ G x y) ↔
    hermDual G Λ =
      ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • Λ := by sorry
