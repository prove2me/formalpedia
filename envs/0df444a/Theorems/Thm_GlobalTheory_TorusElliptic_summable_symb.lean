-- Prove2me | Theorems.Thm_GlobalTheory_TorusElliptic_summable_symb
-- name    : GlobalTheory.TorusElliptic.summable_symb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:58.327213+00:00
-- url     : https://prove2.me/theorems/2a1cc0f9-ee8d-4ca6-a03f-2df2badb0157
-- title:
--   Torus Elliptic: summable symb
-- statement:
--   The Torus Elliptic construction uses the summable symb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean#L94-L101

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

theorem GlobalTheory.TorusElliptic.summable_symb {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) :
    Summable (fun ν : Fin n → ℤ => ‖2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν‖) := by sorry
