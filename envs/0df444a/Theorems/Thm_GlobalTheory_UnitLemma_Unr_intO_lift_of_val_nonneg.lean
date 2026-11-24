-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO_lift_of_val_nonneg
-- name    : GlobalTheory.UnitLemma.Unr.intO_lift_of_val_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:55.724358+00:00
-- url     : https://prove2.me/theorems/3deb726c-be9e-4e6f-937b-915c142f207e
-- title:
--   Unr: int O lift of val nonneg
-- statement:
--   The Unr construction uses the int O lift of val nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExt.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExt.lean#L12-L19

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

theorem GlobalTheory.UnitLemma.Unr.intO_lift_of_val_nonneg (K : UQ) (x : K.E) (h : 0 ≤ val K.O x) : ∃ a : K.O, algebraMap K.O K.E a = x := by sorry
