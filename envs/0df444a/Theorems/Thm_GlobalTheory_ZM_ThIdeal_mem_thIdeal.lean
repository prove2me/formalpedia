-- Prove2me | Theorems.Thm_GlobalTheory_ZM_ThIdeal_mem_thIdeal
-- name    : GlobalTheory.ZM.ThIdeal.mem_thIdeal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:02:51.25628+00:00
-- url     : https://prove2.me/theorems/7b254f41-262a-4eb6-b504-37354b8bc0b2
-- title:
--   Th Ideal: mem th Ideal
-- statement:
--   The Th Ideal construction uses the mem th Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaPointsVanishingIdealRadicalHomogeneous.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaPointsVanishingIdealRadicalHomogeneous.lean#L73-L76

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

theorem GlobalTheory.ZM.ThIdeal.mem_thIdeal {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} (em : o →+* ℂ)
    (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (F : MvPolynomial (Ix g (N' ^ 2)) o) :
    F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v → MvPolynomial.eval₂Hom em v F = 0 := by sorry
