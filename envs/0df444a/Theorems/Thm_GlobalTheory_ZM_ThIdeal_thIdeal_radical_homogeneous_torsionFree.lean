-- Prove2me | Theorems.Thm_GlobalTheory_ZM_ThIdeal_thIdeal_radical_homogeneous_torsionFree
-- name    : GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:01.093311+00:00
-- url     : https://prove2.me/theorems/89ade3fe-4513-43ea-ac1b-8e76f4d7a52e
-- title:
--   Th Ideal: th Ideal radical homogeneous torsion Free
-- statement:
--   The Th Ideal construction uses the th Ideal radical homogeneous torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaPointsVanishingIdealRadicalHomogeneous.lean#L78-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaPointsVanishingIdealRadicalHomogeneous.lean#L78-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaPointsVanishingIdealRadicalHomogeneous
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ThIdeal

theorem GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by sorry
