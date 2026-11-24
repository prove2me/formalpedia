-- Prove2me | Theorems.Thm_GlobalTheory_entire_antilinear_periods_const
-- name    : GlobalTheory.entire_antilinear_periods_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:35.51226+00:00
-- url     : https://prove2.me/theorems/d6ad4ab5-499a-4499-8e53-8b899aad0e46
-- title:
--   Global Theory: entire antilinear periods const
-- statement:
--   The Global Theory construction uses the entire antilinear periods const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EntireAntilinearLatticePeriodsConst.lean#L85-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EntireAntilinearLatticePeriodsConst.lean#L85-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory

theorem GlobalTheory.entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by sorry
