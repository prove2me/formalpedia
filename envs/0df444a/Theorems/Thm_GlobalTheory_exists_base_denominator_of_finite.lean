-- Prove2me | Theorems.Thm_GlobalTheory_exists_base_denominator_of_finite
-- name    : GlobalTheory.exists_base_denominator_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:21.339561+00:00
-- url     : https://prove2.me/theorems/af99d064-99a4-49ff-9561-d32247b08961
-- title:
--   Global Theory: exists base denominator of finite
-- statement:
--   The Global Theory construction uses the exists base denominator of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitMapOfMemNonZeroDivisorsTensor.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitMapOfMemNonZeroDivisorsTensor.lean#L6-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_base_denominator_of_finite {T C K : Type} [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field K] [Algebra T C] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [IsScalarTower T C K] [Module.Finite T C] (k : K) :
    ∃ t : T, t ≠ 0 ∧ ∃ c : C, algebraMap T K t * k = algebraMap C K c := by sorry
