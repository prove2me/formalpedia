-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicCousin_antilin_apply
-- name    : GlobalTheory.PeriodicCousin.antilin_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:14.77424+00:00
-- url     : https://prove2.me/theorems/a6350797-37ff-4894-82c7-19ed24537b81
-- title:
--   Periodic Cousin: antilin apply
-- statement:
--   The Periodic Cousin construction uses the antilin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean#L65-L66

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

theorem GlobalTheory.PeriodicCousin.antilin_apply (t z : Fin g → ℂ) : antilin t z = t ⬝ᵥ star z := by sorry
