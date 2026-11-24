-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_le_integral_inv_log
-- name    : GlobalTheory.CompanionTheory.PrimesAP.le_integral_inv_log
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:54.245808+00:00
-- url     : https://prove2.me/theorems/4c45ae8c-e8b5-4d68-8d44-cf1d239f826c
-- title:
--   Primes AP: le integral inv log
-- statement:
--   The Primes AP construction uses the le integral inv log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimesInProgressionsRelativeOfTzRat.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimesInProgressionsRelativeOfTzRat.lean#L29-L36

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

theorem GlobalTheory.CompanionTheory.PrimesAP.le_integral_inv_log {Y X : ℝ} (hY : 2 ≤ Y) (hX : Y ≤ X) :
    (X - Y) / Real.log X ≤ ∫ t in Y..X, 1 / Real.log t := by sorry
