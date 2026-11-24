-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_eval_temperate
-- name    : GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:41.334198+00:00
-- url     : https://prove2.me/theorems/5d9c128d-e953-46df-bdb8-efd36f31e2dc
-- title:
--   Poly Gauss Schwartz: eval temperate
-- statement:
--   The Poly Gauss Schwartz construction uses the eval temperate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L24-L43

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

theorem GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by sorry
