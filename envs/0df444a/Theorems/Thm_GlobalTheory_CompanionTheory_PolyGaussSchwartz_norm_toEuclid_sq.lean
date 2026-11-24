-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_norm_toEuclid_sq
-- name    : GlobalTheory.CompanionTheory.PolyGaussSchwartz.norm_toEuclid_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:56.199905+00:00
-- url     : https://prove2.me/theorems/0f156c02-2663-4d89-a9d7-947de1fc840a
-- title:
--   Poly Gauss Schwartz: norm to Euclid sq
-- statement:
--   The Poly Gauss Schwartz construction uses the norm to Euclid sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L51-L56

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}

theorem GlobalTheory.CompanionTheory.PolyGaussSchwartz.norm_toEuclid_sq (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by sorry
