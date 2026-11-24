-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_coord_temperate
-- name    : GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord_temperate
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:59.233813+00:00
-- url     : https://prove2.me/theorems/0a54a9cb-18b7-4b41-a525-af140d31050b
-- title:
--   Poly Gauss Schwartz: coord temperate
-- statement:
--   The Poly Gauss Schwartz construction uses the coord temperate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L17-L22

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

theorem GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord_temperate (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by sorry
