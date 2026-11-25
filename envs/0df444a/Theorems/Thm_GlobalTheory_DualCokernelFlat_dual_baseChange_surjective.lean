-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernelFlat_dual_baseChange_surjective
-- name    : GlobalTheory.DualCokernelFlat.dual_baseChange_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:12.295395+00:00
-- url     : https://prove2.me/theorems/e67f738a-9280-4141-8541-1d161c590ba8
-- title:
--   Dual Cokernel Flat: dual base Change surjective
-- statement:
--   The Dual Cokernel Flat construction uses the dual base Change surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L14-L23

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

theorem GlobalTheory.DualCokernelFlat.dual_baseChange_surjective (hs : Surjective (algebraMap A B)) (M : Type) [AddCommGroup M]
    [Module A M] [Module.Projective A M] :
    Surjective (Module.Dual.baseChange B : Module.Dual A M → Module.Dual B (B ⊗[A] M)) := by sorry
