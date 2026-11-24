-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_relLength_span
-- name    : GlobalTheory.SignedLengthOrdFracDet.relLength_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:12:17.443944+00:00
-- url     : https://prove2.me/theorems/b5c6f8d4-165d-4e82-a3ce-433176206045
-- title:
--   Signed Length Ord Frac Det: rel Length span
-- statement:
--   The Signed Length Ord Frac Det construction uses the rel Length span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L83-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L83-L105

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

theorem GlobalTheory.SignedLengthOrdFracDet.relLength_span {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a c : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R) (hP : P.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, P i j • a i) :
    span R (Set.range c) ≤ span R (Set.range a) ∧
      relLength (span R (Set.range a)) (span R (Set.range c)) = Ring.ord R P.det := by sorry
