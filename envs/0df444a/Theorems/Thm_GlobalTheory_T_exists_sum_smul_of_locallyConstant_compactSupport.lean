-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_sum_smul_of_locallyConstant_compactSupport
-- name    : GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:33:29.4818+00:00
-- url     : https://prove2.me/theorems/91f71fd2-dd0e-4895-a930-9fb2436323ed
-- title:
--   T: exists sum smul of locally Constant compact Support
-- statement:
--   The T construction uses the exists sum smul of locally Constant compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumSmulOfLocallyConstantCompactSupportStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumSmulOfLocallyConstantCompactSupportStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumSmulOfLocallyConstantCompactSupport
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumSmulOfLocallyConstantCompactSupportStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport : ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V] [Module ℂ V] (T : Z → V) (_ : IsLocallyConstant T) (K : Set Z) (_ : IsCompact K) (_ : ∀ y, y ∉ K → T y = 0), ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by sorry
