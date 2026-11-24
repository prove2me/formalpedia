-- Prove2me | Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_length_coker_of_injective
-- name    : GlobalTheory.RelativeLengthSpanDet.length_coker_of_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:16.023835+00:00
-- url     : https://prove2.me/theorems/bbea5792-1967-40c9-a77f-341db38404a1
-- title:
--   Relative Length Span Det: length coker of injective
-- statement:
--   The Relative Length Span Det construction uses the length coker of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L44-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L44-L75

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelativeLengthSpanDet
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RelativeLengthSpanDet.length_coker_of_injective {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by sorry
