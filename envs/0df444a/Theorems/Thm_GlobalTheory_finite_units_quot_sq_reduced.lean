-- Prove2me | Theorems.Thm_GlobalTheory_finite_units_quot_sq_reduced
-- name    : GlobalTheory.finite_units_quot_sq_reduced
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:15.06024+00:00
-- url     : https://prove2.me/theorems/0a5589eb-aab2-463d-b93f-078141a57bc4
-- title:
--   Global Theory: finite units quot sq reduced
-- statement:
--   The Global Theory construction uses the finite units quot sq reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L104-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L104-L154

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

theorem GlobalTheory.finite_units_quot_sq_reduced (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (K : Type) [CommRing K] [Algebra F K] [Module.Finite F K]
    [IsReduced K] : Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by sorry
