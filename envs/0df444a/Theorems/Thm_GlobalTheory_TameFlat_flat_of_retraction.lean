-- Prove2me | Theorems.Thm_GlobalTheory_TameFlat_flat_of_retraction
-- name    : GlobalTheory.TameFlat.flat_of_retraction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:02:40.369652+00:00
-- url     : https://prove2.me/theorems/281f9fc1-cd28-4643-82c8-2b16ad12c7dd
-- title:
--   Tame Flat: flat of retraction
-- statement:
--   The Tame Flat construction uses the flat of retraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfTameDescent.lean#L34-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfTameDescent.lean#L34-L98

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

theorem GlobalTheory.TameFlat.flat_of_retraction {A B R : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R] (e : B →ₗ[A] A) (he : e 1 = 1)
    [Module.Flat B (B ⊗[A] R)] : Module.Flat A R := by sorry
