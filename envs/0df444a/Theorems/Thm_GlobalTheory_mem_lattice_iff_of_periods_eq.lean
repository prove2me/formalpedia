-- Prove2me | Theorems.Thm_GlobalTheory_mem_lattice_iff_of_periods_eq
-- name    : GlobalTheory.mem_lattice_iff_of_periods_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:16.694653+00:00
-- url     : https://prove2.me/theorems/1ce23572-840e-4db7-b3ba-0f98c1d7d52a
-- title:
--   Global Theory: mem lattice iff of periods eq
-- statement:
--   The Global Theory construction uses the mem lattice iff of periods eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L141-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory

theorem GlobalTheory.mem_lattice_iff_of_periods_eq {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) (x : ℂ) :
    x ∈ L.lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by sorry
