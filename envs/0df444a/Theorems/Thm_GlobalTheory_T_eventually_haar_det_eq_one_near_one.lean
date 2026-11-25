-- Prove2me | Theorems.Thm_GlobalTheory_T_eventually_haar_det_eq_one_near_one
-- name    : GlobalTheory.T.eventually_haar_det_eq_one_near_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:19.110862+00:00
-- url     : https://prove2.me/theorems/fdc51ada-abae-5c02-a609-d7e962c06607
-- title:
--   T: eventually haar det eq one near one
-- statement:
--   The T construction uses the eventually haar det eq one near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyHaarDetEqOneNearOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyHaarDetEqOneNearOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyHaarDetEqOneNearOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyHaarDetEqOneNearOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eventually_haar_det_eq_one_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k), MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by sorry
