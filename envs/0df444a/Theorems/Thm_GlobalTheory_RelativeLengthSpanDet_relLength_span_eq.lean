-- Prove2me | Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_relLength_span_eq
-- name    : GlobalTheory.RelativeLengthSpanDet.relLength_span_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:59.629861+00:00
-- url     : https://prove2.me/theorems/41d86a7e-465d-4f4c-801f-33a2e428ed83
-- title:
--   Relative Length Span Det: rel Length span eq
-- statement:
--   The Relative Length Span Det construction uses the rel Length span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanEqAddValDet.lean#L111-L117

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
universe u_1 u_2 u_3 in

theorem GlobalTheory.RelativeLengthSpanDet.relLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {V : Type u_2} [AddCommGroup V] [Module R V] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {a v : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R)
    (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      (addVal R : R → ℕ∞) P.det := by sorry
