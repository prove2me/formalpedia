-- Prove2me | Theorems.Thm_GlobalTheory_Cube_sum_parts
-- name    : GlobalTheory.Cube.sum_parts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:41:28.718894+00:00
-- url     : https://prove2.me/theorems/93778d67-4bd5-5a8f-8458-53080cc41e46
-- title:
--   Cube: sum parts
-- statement:
--   The Cube construction uses the sum parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L413-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L413-L417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]

theorem GlobalTheory.Cube.sum_parts {M : Type*} [AddCommMonoid M] (w : Finset (ι ⊕ₗ κ)) (F : ι ⊕ₗ κ → M) :
    ∑ j ∈ w, F j = ∑ i ∈ part (inlEmb ι κ) w, F (inlEmb ι κ i) +
      ∑ k ∈ part (inrEmb ι κ) w, F (inrEmb ι κ k) := by sorry
