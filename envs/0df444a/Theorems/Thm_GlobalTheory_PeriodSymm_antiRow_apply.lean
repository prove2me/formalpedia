-- Prove2me | Theorems.Thm_GlobalTheory_PeriodSymm_antiRow_apply
-- name    : GlobalTheory.PeriodSymm.antiRow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:30.475048+00:00
-- url     : https://prove2.me/theorems/e1fa23c0-9ee0-4b0e-93f0-ce5bcf3d895c
-- title:
--   Period Symm: anti Row apply
-- statement:
--   The Period Symm construction uses the anti Row apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaCocyclePeriodicNonvanishingSections.lean#L300-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaCocyclePeriodicNonvanishingSections.lean#L300-L301

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

theorem GlobalTheory.PeriodSymm.antiRow_apply {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) (z : Fin g → ℂ) :
    antiRow M m z = M.mulVec (star z) m := by sorry
