-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_StabIndex_isUnit_algebraMap
-- name    : GlobalTheory.UnitLemma.StabIndex.isUnit_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:16.326028+00:00
-- url     : https://prove2.me/theorems/e596fc3a-d7d3-4675-b1fc-b95c7973e300
-- title:
--   Stab Index: is Unit algebra Map
-- statement:
--   The Stab Index construction uses the is Unit algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelIndexNeZeroOfBetween.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelIndexNeZeroOfBetween.lean#L37-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexNeZeroOfBetween
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.StabIndex

theorem GlobalTheory.UnitLemma.StabIndex.isUnit_algebraMap (K : UQ) (B : InvAlg K) (c : K.O) (hc : c ≠ 0) :
    IsUnit (algebraMap K.O B.A c) := by sorry
