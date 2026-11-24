-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_EFf_eq
-- name    : GlobalTheory.eq_of_EFf_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:39.393208+00:00
-- url     : https://prove2.me/theorems/bc50ccc0-2d5e-424c-b0d5-c8a8fe4418a3
-- title:
--   Global Theory: eq of EFf eq
-- statement:
--   The Global Theory construction uses the eq of EFf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L382-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L382-L388

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

theorem GlobalTheory.eq_of_EFf_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0) (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ)
    {x x' : Fin r → E} (h : ∀ y ∈ Λ, EFf ξ G x y = EFf ξ G x' y) : x = x' := by sorry
