-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
-- name    : GroundTheory.Global.Elliptic.IsPeriodic.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:29.346962+00:00
-- url     : https://prove2.me/theorems/01f95321-aaca-40f3-a0bd-2b570c8a9c07
-- title:
--   Is Periodic: sub
-- statement:
--   The Is Periodic construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L40-L42

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

theorem GroundTheory.Global.Elliptic.IsPeriodic.sub {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : f (z - l) = f z := by sorry
