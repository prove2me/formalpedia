-- Prove2me | Theorems.Thm_GlobalTheory_plane_lattice_short_basis
-- name    : GlobalTheory.plane_lattice_short_basis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:06.622141+00:00
-- url     : https://prove2.me/theorems/3b5f39e9-9169-4e91-8e6e-3654eafed139
-- title:
--   Global Theory: plane lattice short basis
-- statement:
--   The Global Theory construction uses the plane lattice short basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PlaneLatticeShortBasisOfBoundPowTwo.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PlaneLatticeShortBasisOfBoundPowTwo.lean#L81-L89

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

theorem GlobalTheory.plane_lattice_short_basis : ∀ e₁ e₂ : ℂ, ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by sorry
