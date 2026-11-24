-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicCousin_contDiffAt_fderiv
-- name    : GlobalTheory.PeriodicCousin.contDiffAt_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:50.0646+00:00
-- url     : https://prove2.me/theorems/0440a88b-e69b-410b-9220-f733e51ad0c0
-- title:
--   Periodic Cousin: cont Diff At fderiv
-- statement:
--   The Periodic Cousin construction uses the cont Diff At fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean#L27-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicCousin
variable {g : ℕ}

theorem GlobalTheory.PeriodicCousin.contDiffAt_fderiv {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fderiv ℝ f) z := by sorry
