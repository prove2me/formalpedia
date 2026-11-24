-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO_val_ne_zero_of_mem
-- name    : GlobalTheory.UnitLemma.Unr.intO_val_ne_zero_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:58.377677+00:00
-- url     : https://prove2.me/theorems/aaf97d39-2fc0-442b-8180-4de5476c5618
-- title:
--   Unr: int O val ne zero of mem
-- statement:
--   The Unr construction uses the int O val ne zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExt.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExt.lean#L31-L39

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

theorem GlobalTheory.UnitLemma.Unr.intO_val_ne_zero_of_mem (K : UQ) (a : K.O) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal K.O) :
    val K.O (algebraMap K.O K.E a) ≠ 0 := by sorry
