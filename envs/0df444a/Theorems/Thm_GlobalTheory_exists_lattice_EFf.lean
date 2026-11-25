-- Prove2me | Theorems.Thm_GlobalTheory_exists_lattice_EFf
-- name    : GlobalTheory.exists_lattice_EFf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:17.285222+00:00
-- url     : https://prove2.me/theorems/ab055516-c789-40a1-8f22-fb683dea565a
-- title:
--   Global Theory: exists lattice EFf
-- statement:
--   The Global Theory construction uses the exists lattice EFf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/TraceFormBilinSeparatingLeftIff.lean#L422-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/TraceFormBilinSeparatingLeftIff.lean#L422-L435

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.FD hiding cc_cc cc_sub cc_mul cc_one cc_zero cc_eq_zero
open ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup M'] [Module (𝓞 E) M']

theorem GlobalTheory.exists_lattice_EFf [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M]
    (hr : Module.finrank (𝓞 E) M = r) {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {β : LinearMap.BilinForm ℤ M} (halt : ∀ x, β x x = 0) (hβ : IsIntConjAdj E β)
    (hu : Function.Bijective β) :
    ∃ (φ : M →ₗ[𝓞 E] (Fin r → E)) (G : Matrix (Fin r) (Fin r) E),
      Function.Injective φ ∧ IsLattice (LinearMap.range φ) ∧ (∀ a b, cc (G a b) = G b a) ∧
      G.det ≠ 0 ∧ (∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) ∧
      (∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ, ∃ k : ℤ, EFf ξ0 G x y = k) ∧
      ∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
        (f y : ℚ) = EFf ξ0 G x y := by sorry
