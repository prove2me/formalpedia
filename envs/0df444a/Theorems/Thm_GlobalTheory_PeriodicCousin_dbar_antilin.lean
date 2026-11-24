-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicCousin_dbar_antilin
-- name    : GlobalTheory.PeriodicCousin.dbar_antilin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:44:28.978478+00:00
-- url     : https://prove2.me/theorems/fa8f9b65-aa61-4bfc-8227-eb24b1a6ae76
-- title:
--   Periodic Cousin: dbar antilin
-- statement:
--   The Periodic Cousin construction uses the dbar antilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean#L68-L77

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

theorem GlobalTheory.PeriodicCousin.dbar_antilin (t z : Fin g → ℂ) (a : Fin g) : dbar a (antilin t) z = 2 * t a := by sorry
