-- Prove2me | Theorems.Thm_GlobalTheory_TorusElliptic_sum_fderiv
-- name    : GlobalTheory.TorusElliptic.sum_fderiv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:54.83112+00:00
-- url     : https://prove2.me/theorems/d12f33d7-9d1a-4389-9c4c-b708d6dfbdc1
-- title:
--   Torus Elliptic: sum fderiv
-- statement:
--   The Torus Elliptic construction uses the sum fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L103-L117

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

theorem GlobalTheory.TorusElliptic.sum_fderiv {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) (x : Fin n → ℝ) :
    ∑ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν, 2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν * ch ν x := by sorry
