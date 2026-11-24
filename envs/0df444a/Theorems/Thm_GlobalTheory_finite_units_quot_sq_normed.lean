-- Prove2me | Theorems.Thm_GlobalTheory_finite_units_quot_sq_normed
-- name    : GlobalTheory.finite_units_quot_sq_normed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:06.951803+00:00
-- url     : https://prove2.me/theorems/455713f5-38ff-4c50-9ff2-e4f226103b19
-- title:
--   Global Theory: finite units quot sq normed
-- statement:
--   The Global Theory construction uses the finite units quot sq normed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L8-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L8-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.finite_units_quot_sq_normed (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (R : Type) [NormedCommRing R] [Nontrivial R] [NormedAlgebra F R]
    [Module.Finite F R] (hR : ∀ x : R, x ≠ 0 → IsUnit x) :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by sorry
