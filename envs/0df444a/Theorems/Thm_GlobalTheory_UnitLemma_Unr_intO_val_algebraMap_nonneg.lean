-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO_val_algebraMap_nonneg
-- name    : GlobalTheory.UnitLemma.Unr.intO_val_algebraMap_nonneg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:49.255574+00:00
-- url     : https://prove2.me/theorems/1d2802cd-308f-41b0-9f18-cf0127c3e281
-- title:
--   Unr: int O val algebra Map nonneg
-- statement:
--   The Unr construction uses the int O val algebra Map nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExt.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExt.lean#L21-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.intO_val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by sorry
