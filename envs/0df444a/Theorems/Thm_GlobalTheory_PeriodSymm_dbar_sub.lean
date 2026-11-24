-- Prove2me | Theorems.Thm_GlobalTheory_PeriodSymm_dbar_sub
-- name    : GlobalTheory.PeriodSymm.dbar_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:57.250859+00:00
-- url     : https://prove2.me/theorems/40dbda3a-ed91-4a5a-aee1-5db441f3ed59
-- title:
--   Period Symm: dbar sub
-- statement:
--   The Period Symm construction uses the dbar sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaCocyclePeriodicNonvanishingSections.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaCocyclePeriodicNonvanishingSections.lean#L34-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.PeriodSymm.dbar_sub {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x - f' x) u z = dbar f u z - dbar f' u z := by sorry
