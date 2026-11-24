-- Prove2me | Theorems.Thm_GlobalTheory_plane_lattice_short_basis_of_bound_pow_two
-- name    : GlobalTheory.plane_lattice_short_basis_of_bound_pow_two
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:17.20138+00:00
-- url     : https://prove2.me/theorems/410af766-8ecc-4f13-91cb-47b2617cdc89
-- title:
--   Global Theory: plane lattice short basis of bound pow two
-- statement:
--   The Global Theory construction uses the plane lattice short basis of bound pow two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PlaneLatticeShortBasisOfBoundPowTwo.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PlaneLatticeShortBasisOfBoundPowTwo.lean#L61-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.plane_lattice_short_basis_of_bound_pow_two (n : ℕ) : ∀ e₁ e₂ : ℂ,
    ‖e₁‖ ^ 2 ≤ 2 ^ n * (2 * |((starRingEnd ℂ) e₁ * e₂).im|) →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by sorry
