-- Prove2me | Theorems.Thm_GlobalTheory_T_unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
-- name    : GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:40:15.643319+00:00
-- url     : https://prove2.me/theorems/b87ad618-5d30-5cd7-a38a-02dce7a7a1f7
-- title:
--   T: unit Indicator Hermitian Block lift Last Basis of norm le one
-- statement:
--   The T construction uses the unit Indicator Hermitian Block lift Last Basis of norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorHermitianBlockLiftLastBasisOfNormLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement
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

theorem GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by sorry
