-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalModule_distribHaarChar_det_eventually_eq_one
-- name    : GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:20.193992+00:00
-- url     : https://prove2.me/theorems/e495d681-7667-4683-be2a-517e7c022f51
-- title:
--   Local Module: distrib Haar Char det eventually eq one
-- statement:
--   The Local Module construction uses the distrib Haar Char det eventually eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyHaarDetEqOneNearOne.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyHaarDetEqOneNearOne.lean#L9-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DistribHaarCharEqOneOfValuationEqOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyHaarDetEqOneNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel MeasureTheory
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalModule

theorem GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k),
        MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by sorry
