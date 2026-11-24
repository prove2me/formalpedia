-- Prove2me | Theorems.Thm_GlobalTheory_DiscConductor_exists_conductor_of_fractionFields
-- name    : GlobalTheory.DiscConductor.exists_conductor_of_fractionFields
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:57.442893+00:00
-- url     : https://prove2.me/theorems/76fd21e1-6afe-4470-b4ce-00ab81b9dfab
-- title:
--   Disc Conductor: exists conductor of fraction Fields
-- statement:
--   The Disc Conductor construction uses the exists conductor of fraction Fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DiscrMulMemOfIsIntegral.lean#L71-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DiscrMulMemOfIsIntegral.lean#L71-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFieldsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial
open GlobalTheory GlobalTheory.DiscConductor

theorem GlobalTheory.DiscConductor.exists_conductor_of_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T]
    [CommRing U] [IsDomain U] [IsIntegrallyClosed U]
    [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K]
    [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L]
    [Module.Flat T U] [Module.Finite T C] :
    ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c →
      ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s =
        algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by sorry
