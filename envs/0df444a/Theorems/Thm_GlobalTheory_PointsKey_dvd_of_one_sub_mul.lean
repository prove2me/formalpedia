-- Prove2me | Theorems.Thm_GlobalTheory_PointsKey_dvd_of_one_sub_mul
-- name    : GlobalTheory.PointsKey.dvd_of_one_sub_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:29.550407+00:00
-- url     : https://prove2.me/theorems/65c78f9f-4c91-415d-9de9-0e9bb766f1cf
-- title:
--   Points Key: dvd of one sub mul
-- statement:
--   The Points Key construction uses the dvd of one sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdAllPowOfFrobeniusEqKilledByPerfectPoints.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdAllPowOfFrobeniusEqKilledByPerfectPoints.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.PointsKey

theorem GlobalTheory.PointsKey.dvd_of_one_sub_mul {R : Type} [CommRing R] (u r D a : R) (m : ℕ)
    (h : (1 - u * r) * D = u ^ m * a) : u ^ m ∣ D := by sorry
