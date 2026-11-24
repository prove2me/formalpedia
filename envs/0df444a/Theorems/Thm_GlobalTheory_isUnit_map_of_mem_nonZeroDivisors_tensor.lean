-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_map_of_mem_nonZeroDivisors_tensor
-- name    : GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:58.154287+00:00
-- url     : https://prove2.me/theorems/25408c0b-ef40-4002-b0bc-b63cdefd361e
-- title:
--   Global Theory: is Unit map of mem non Zero Divisors tensor
-- statement:
--   The Global Theory construction uses the is Unit map of mem non Zero Divisors tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitMapOfMemNonZeroDivisorsTensor.lean#L52-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitMapOfMemNonZeroDivisorsTensor.lean#L52-L109

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

theorem GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor (T U C F K L : Type) [CommRing T] [IsDomain T]
    [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K]
    [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L]
    [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C]
    (φ : U ⊗[T] C →+* L ⊗[F] K) (hinj : Function.Injective φ)
    (hφ : ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) :
    ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by sorry
