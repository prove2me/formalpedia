-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_of_isPushout
-- name    : GlobalTheory.FieldBaseChange.isExtension_of_isPushout
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:16.148982+00:00
-- url     : https://prove2.me/theorems/dbff7ec3-0afa-4462-8f2e-132aaca95387
-- title:
--   Field Base Change: is Extension of is Pushout
-- statement:
--   The Field Base Change construction uses the is Extension of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L145-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L145-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]

theorem GlobalTheory.FieldBaseChange.isExtension_of_isPushout {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra F B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [IsScalarTower K F B] [H : Algebra.IsPushout K F A B]
    (a : A →ₛₗ[algebraMap K F] B) (ha : ∀ x, a x = algebraMap A B x) : IsExtension a := by sorry
