-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_units_quot_sq_finiteEtaleHermitianPair
-- name    : GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:40.392519+00:00
-- url     : https://prove2.me/theorems/8ea4bf6a-eaf7-45aa-9ddd-196220c88728
-- title:
--   T: finite units quot sq finite Etale Hermitian Pair
-- statement:
--   The T construction uses the finite units quot sq finite Etale Hermitian Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by sorry
