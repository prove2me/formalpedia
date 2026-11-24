-- Prove2me | Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_summable
-- name    : GlobalTheory.TorusElliptic.Rapid.summable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:47.124217+00:00
-- url     : https://prove2.me/theorems/31316d46-0688-40dd-bae8-1923e07c2950
-- title:
--   Rapid: summable
-- statement:
--   The Rapid construction uses the summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L58-L71

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

theorem GlobalTheory.TorusElliptic.Rapid.summable {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) :
    Summable (fun ν => ‖c ν‖) := by sorry
