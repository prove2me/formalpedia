-- Prove2me | Theorems.Thm_GlobalTheory_datum_exists_lattice_EFf
-- name    : GlobalTheory.datum_exists_lattice_EFf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:37:50.65361+00:00
-- url     : https://prove2.me/theorems/e3bd4211-f632-469e-bed4-e391cf59529e
-- title:
--   Global Theory: datum exists lattice EFf
-- statement:
--   The Global Theory construction uses the datum exists lattice EFf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/TraceFormBilinSeparatingLeftIff.lean#L490-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/TraceFormBilinSeparatingLeftIff.lean#L490-L498

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {H : Host E}

theorem GlobalTheory.datum_exists_lattice_EFf (D : Datum H) {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    ∃ (Λ : Submodule (𝓞 E) (Fin (D.p + D.q) → E)) (e : D.La ≃ₗ[𝓞 E] Λ)
      (G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) E),
      IsLattice Λ ∧ (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      (∀ x y, EFf ξ0 G (e x) (e y) = D.EF x y) ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k) ∧
      ∀ f : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (f y : ℚ) = EFf ξ0 G x y := by sorry
