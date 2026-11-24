-- Prove2me | Theorems.Thm_GlobalTheory_finite_units_quot_sq_field
-- name    : GlobalTheory.finite_units_quot_sq_field
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:16.638093+00:00
-- url     : https://prove2.me/theorems/0bee7984-22e5-400d-95cf-26d201a1498f
-- title:
--   Global Theory: finite units quot sq field
-- statement:
--   The Global Theory construction uses the finite units quot sq field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L89-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L89-L102

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

theorem GlobalTheory.finite_units_quot_sq_field (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (L : Type) [Field L] [Algebra F L] [Module.Finite F L] :
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by sorry
