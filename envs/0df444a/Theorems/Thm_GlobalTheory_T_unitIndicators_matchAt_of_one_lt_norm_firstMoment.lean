-- Prove2me | Theorems.Thm_GlobalTheory_T_unitIndicators_matchAt_of_one_lt_norm_firstMoment
-- name    : GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:40:14.394424+00:00
-- url     : https://prove2.me/theorems/9a969765-a367-5d46-8034-15d130062d31
-- title:
--   T: unit Indicators match At of one lt norm first Moment
-- statement:
--   The T construction uses the unit Indicators match At of one lt norm first Moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMomentStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMomentStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorsMatchAtOfOneLtNormFirstMoment
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorsMatchAtOfOneLtNormFirstMomentStatement
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

theorem GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by sorry
