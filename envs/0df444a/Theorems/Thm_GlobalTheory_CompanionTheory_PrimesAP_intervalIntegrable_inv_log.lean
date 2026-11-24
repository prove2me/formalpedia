-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_intervalIntegrable_inv_log
-- name    : GlobalTheory.CompanionTheory.PrimesAP.intervalIntegrable_inv_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:09.40171+00:00
-- url     : https://prove2.me/theorems/16c73e2f-7a88-4706-83d9-bc5654944008
-- title:
--   Primes AP: interval Integrable inv log
-- statement:
--   The Primes AP construction uses the interval Integrable inv log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimesInProgressionsRelativeOfTzRat.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimesInProgressionsRelativeOfTzRat.lean#L17-L27

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset DirichletCharacter
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesAP

theorem GlobalTheory.CompanionTheory.PrimesAP.intervalIntegrable_inv_log {Y X : ℝ} (hY : 2 ≤ Y) (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume Y X := by sorry
