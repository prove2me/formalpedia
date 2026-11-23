-- Prove2me | Theorems.Thm_GlobalTheory_mem_lattice_periodPairOfTau
-- name    : GlobalTheory.mem_lattice_periodPairOfTau
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:20.585898+00:00
-- url     : https://prove2.me/theorems/6bbfcb6c-290d-4db9-b731-1ef69eb30dfe
-- title:
--   Global Theory: mem lattice period Pair Of Tau
-- statement:
--   The Global Theory construction uses the mem lattice period Pair Of Tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean#L33-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
open GlobalTheory

theorem GlobalTheory.mem_lattice_periodPairOfTau (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau τ).lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by sorry
