-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolPQ_continuous_hs_umat
-- name    : GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:39.969424+00:00
-- url     : https://prove2.me/theorems/fac71f73-36f9-471d-af62-6a7a01da0eb9
-- title:
--   Hol PQ: continuous hs umat
-- statement:
--   The Hol PQ construction uses the continuous hs umat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/OneAddHsInvPowLintegralLtTop.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/OneAddHsInvPowLintegralLtTop.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_OneAddHsInvPowLintegralLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolPQ

theorem GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat {n : ℕ} (ε : Fin n → Bool) :
    Continuous fun g : UJ ε => hs (umat g) := by sorry
