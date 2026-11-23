-- Prove2me | Theorems.Thm_GlobalTheory_DiscConductor_isIntegral_trace_of_isIntegral
-- name    : GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:51.056891+00:00
-- url     : https://prove2.me/theorems/53f41c1d-4160-456b-a386-d019a5fbb2d9
-- title:
--   Disc Conductor: is Integral trace of is Integral
-- statement:
--   The Disc Conductor construction uses the is Integral trace of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DiscrMulMemOfIsIntegral.lean#L11-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DiscrMulMemOfIsIntegral.lean#L11-L41

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

theorem GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral
    (U L Ω : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω] [Algebra U Ω]
    [IsScalarTower U L Ω] [Module.Finite L Ω] (ω : Ω) (h : IsIntegral U ω) :
    IsIntegral U (Algebra.trace L Ω ω) := by sorry
