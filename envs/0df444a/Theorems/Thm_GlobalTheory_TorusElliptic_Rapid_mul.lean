-- Prove2me | Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_mul
-- name    : GlobalTheory.TorusElliptic.Rapid.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:58.571489+00:00
-- url     : https://prove2.me/theorems/1e40850e-4500-4685-9bf8-1922e8df800d
-- title:
--   Rapid: mul
-- statement:
--   The Rapid construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L73-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
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
open GlobalTheory
open GlobalTheory.TorusElliptic

theorem GlobalTheory.TorusElliptic.Rapid.mul {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (z : ℂ) (j : Fin n) :
    Rapid (fun ν => z * (ν j : ℂ) * c ν) := by sorry
