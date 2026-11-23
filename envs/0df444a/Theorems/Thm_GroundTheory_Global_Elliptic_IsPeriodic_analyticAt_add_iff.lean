-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_analyticAt_add_iff
-- name    : GroundTheory.Global.Elliptic.IsPeriodic.analyticAt_add_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:03.546069+00:00
-- url     : https://prove2.me/theorems/b0e56843-d493-4613-bd04-9b0e84f41e2c
-- title:
--   Is Periodic: analytic At add iff
-- statement:
--   The Is Periodic construction uses the analytic At add iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L88-L99

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)
variable {L}

theorem GroundTheory.Global.Elliptic.IsPeriodic.analyticAt_add_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    AnalyticAt ℂ f (z + l) ↔ AnalyticAt ℂ f z := by sorry
