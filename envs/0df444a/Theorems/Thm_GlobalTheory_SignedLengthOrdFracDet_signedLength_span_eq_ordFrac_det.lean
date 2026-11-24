-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_signedLength_span_eq_ordFrac_det
-- name    : GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:35.188861+00:00
-- url     : https://prove2.me/theorems/bbaac91f-4101-4bcd-9ad8-3d7e7d49a9ab
-- title:
--   Signed Length Ord Frac Det: signed Length span eq ord Frac det
-- statement:
--   The Signed Length Ord Frac Det construction uses the signed Length span eq ord Frac det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L107-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L107-L166

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule

theorem GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (span R (Set.range a)) (span R (Set.range b)) ∧
      Ring.ordFrac R g.det =
        WithZero.exp (signedLength (span R (Set.range a)) (span R (Set.range b))) := by sorry
