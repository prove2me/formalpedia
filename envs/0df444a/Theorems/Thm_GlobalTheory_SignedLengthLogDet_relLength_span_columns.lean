-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthLogDet_relLength_span_columns
-- name    : GlobalTheory.SignedLengthLogDet.relLength_span_columns
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:35.031192+00:00
-- url     : https://prove2.me/theorems/320c7749-a823-472d-94ee-d6e6eb1caedd
-- title:
--   Signed Length Log Det: rel Length span columns
-- statement:
--   The Signed Length Log Det construction uses the rel Length span columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthEqLogOrdFracDet.lean#L81-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthEqLogOrdFracDet.lean#L81-L115

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module

theorem GlobalTheory.SignedLengthLogDet.relLength_span_columns {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Submodule R V} (a : Basis ι R A) (h : Matrix ι ι R) (hh : h.det ≠ 0) (v : ι → V)
    (hv : ∀ j, v j = ∑ i, h i j • (a i : V)) :
    Submodule.span R (Set.range v) ≤ A ∧
      relLength A (Submodule.span R (Set.range v)) = Ring.ord R h.det := by sorry
