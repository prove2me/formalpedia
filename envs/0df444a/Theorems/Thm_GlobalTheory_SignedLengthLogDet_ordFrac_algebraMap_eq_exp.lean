-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthLogDet_ordFrac_algebraMap_eq_exp
-- name    : GlobalTheory.SignedLengthLogDet.ordFrac_algebraMap_eq_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:00.900359+00:00
-- url     : https://prove2.me/theorems/4687f0cd-b99e-40d2-8830-6be387c49965
-- title:
--   Signed Length Log Det: ord Frac algebra Map eq exp
-- statement:
--   The Signed Length Log Det construction uses the ord Frac algebra Map eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthEqLogOrdFracDet.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthEqLogOrdFracDet.lean#L117-L123

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module

theorem GlobalTheory.SignedLengthLogDet.ordFrac_algebraMap_eq_exp {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R} (hx : x ≠ 0) {n : ℕ}
    (hn : Ring.ord R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by sorry
