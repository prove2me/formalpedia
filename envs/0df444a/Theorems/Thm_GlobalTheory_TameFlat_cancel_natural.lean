-- Prove2me | Theorems.Thm_GlobalTheory_TameFlat_cancel_natural
-- name    : GlobalTheory.TameFlat.cancel_natural
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:57.136917+00:00
-- url     : https://prove2.me/theorems/b87b9705-418b-50c8-82f3-0d52d6ea7e1b
-- title:
--   Tame Flat: cancel natural
-- statement:
--   The Tame Flat construction uses the cancel natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfTameDescent.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfTameDescent.lean#L16-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TameFlat
open TensorProduct

theorem GlobalTheory.TameFlat.cancel_natural {A B R X Y : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R]
    [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y]
    (f : X →ₗ[B] Y) (t : X ⊗[B] (B ⊗[A] R)) :
    AlgebraTensorModule.cancelBaseChange A B B Y R (f.rTensor _ t) =
      (f.restrictScalars A).rTensor R (AlgebraTensorModule.cancelBaseChange A B B X R t) := by sorry
