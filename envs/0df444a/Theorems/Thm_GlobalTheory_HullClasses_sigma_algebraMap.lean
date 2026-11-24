-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_sigma_algebraMap
-- name    : GlobalTheory.HullClasses.sigma_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:29.594824+00:00
-- url     : https://prove2.me/theorems/9a2ae0a6-8065-428c-bd77-bfdfcd0e8f0d
-- title:
--   Hull Classes: sigma algebra Map
-- statement:
--   The Hull Classes construction uses the sigma algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L71-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.HullClasses.sigma_algebraMap (c cb : K.O) (h : K.c (algebraMap K.O K.E c) = algebraMap K.O K.E cb) :
    B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb := by sorry
