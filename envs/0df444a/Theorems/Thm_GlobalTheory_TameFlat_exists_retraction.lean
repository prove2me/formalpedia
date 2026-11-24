-- Prove2me | Theorems.Thm_GlobalTheory_TameFlat_exists_retraction
-- name    : GlobalTheory.TameFlat.exists_retraction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:02:34.355379+00:00
-- url     : https://prove2.me/theorems/84b4c155-6675-4049-9979-4b8948f12aab
-- title:
--   Tame Flat: exists retraction
-- statement:
--   The Tame Flat construction uses the exists retraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfTameDescent.lean#L100-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfTameDescent.lean#L100-L127

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

theorem GlobalTheory.TameFlat.exists_retraction {Γ A B : Type} [Group Γ] [Finite Γ] [CommRing A] [CommRing B]
    [MulSemiringAction Γ B] [Algebra A B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ]
    (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : ∑ᶠ g : Γ, g • b = 1) :
    ∃ e : B →ₗ[A] A, e 1 = 1 := by sorry
