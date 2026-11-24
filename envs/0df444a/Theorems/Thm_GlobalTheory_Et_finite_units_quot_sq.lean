-- Prove2me | Theorems.Thm_GlobalTheory_Et_finite_units_quot_sq
-- name    : GlobalTheory.Et.finite_units_quot_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:58:12.096269+00:00
-- url     : https://prove2.me/theorems/9b53e17b-8c94-4cdc-96bc-d3022bfe2f10
-- title:
--   Et: finite units quot sq
-- statement:
--   The Et construction uses the finite units quot sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L156-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPair.lean#L156-L163

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

theorem GlobalTheory.Et.finite_units_quot_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E),
    Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by sorry
