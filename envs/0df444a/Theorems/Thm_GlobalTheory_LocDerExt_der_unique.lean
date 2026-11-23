-- Prove2me | Theorems.Thm_GlobalTheory_LocDerExt_der_unique
-- name    : GlobalTheory.LocDerExt.der_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:11.020024+00:00
-- url     : https://prove2.me/theorems/085e7fbc-5ead-4391-bb8f-67e09a874030
-- title:
--   Loc Der Ext: der unique
-- statement:
--   The Loc Der Ext construction uses the der unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationExtensionOfAffine.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationExtensionOfAffine.lean#L14-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.LocDerExt

theorem GlobalTheory.LocDerExt.der_unique {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (δ₁ δ₂ : B → C)
    (h₁ : ∀ a b, δ₁ (a * b) = φ a * δ₁ b + φ b * δ₁ a)
    (h₂ : ∀ a b, δ₂ (a * b) = φ a * δ₂ b + φ b * δ₂ a)
    (h : ∀ a, δ₁ (algebraMap A B a) = δ₂ (algebraMap A B a)) (s : B) : δ₁ s = δ₂ s := by sorry
