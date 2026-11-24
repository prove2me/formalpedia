-- Prove2me | Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_length_coker
-- name    : GlobalTheory.RelativeLengthSpanDet.length_coker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:13.504373+00:00
-- url     : https://prove2.me/theorems/96a99391-ea4c-4225-aa64-11f6f14da9c2
-- title:
--   Relative Length Span Det: length coker
-- statement:
--   The Relative Length Span Det construction uses the length coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L77-L87

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

theorem GlobalTheory.RelativeLengthSpanDet.length_coker (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by sorry
