-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernelFlat_dual_baseChange_dualMap
-- name    : GlobalTheory.DualCokernelFlat.dual_baseChange_dualMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:36.698868+00:00
-- url     : https://prove2.me/theorems/e1ce6991-1870-438d-821d-9122aa7499f1
-- title:
--   Dual Cokernel Flat: dual base Change dual Map
-- statement:
--   The Dual Cokernel Flat construction uses the dual base Change dual Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L41-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernelFlat
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem GlobalTheory.DualCokernelFlat.dual_baseChange_dualMap {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (a : M →ₗ[A] N) (f : Module.Dual A N) :
    Module.Dual.baseChange B (a.dualMap f) =
      (a.baseChange B).dualMap (Module.Dual.baseChange B f) := by sorry
