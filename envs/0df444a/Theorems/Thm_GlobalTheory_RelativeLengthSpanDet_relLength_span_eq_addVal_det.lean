-- Prove2me | Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_relLength_span_eq_addVal_det
-- name    : GlobalTheory.RelativeLengthSpanDet.relLength_span_eq_addVal_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:59.134183+00:00
-- url     : https://prove2.me/theorems/47027bd9-a43d-467b-8840-f1c3eee17da0
-- title:
--   Relative Length Span Det: rel Length span eq add Val det
-- statement:
--   The Relative Length Span Det construction uses the rel Length span eq add Val det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L89-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L89-L107

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

theorem GlobalTheory.RelativeLengthSpanDet.relLength_span_eq_addVal_det {V : Type*} [AddCommGroup V] [Module R V] {a v : ι → V}
    (ha : LinearIndependent R a) (P : Matrix ι ι R) (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      addVal R P.det := by sorry
