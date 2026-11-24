-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_complexExtend
-- name    : GlobalTheory.differentiableOn_complexExtend
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:56.387721+00:00
-- url     : https://prove2.me/theorems/b75038e1-b247-43a0-9643-47ae3aaf2b47
-- title:
--   Global Theory: differentiable On complex Extend
-- statement:
--   The Global Theory construction uses the differentiable On complex Extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnComplexExtend.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnComplexExtend.lean#L56-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnComplexExtend
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
open GlobalTheory

theorem GlobalTheory.differentiableOn_complexExtend {O : Type} [CommRing O] {g m : ℕ}
    {B : Set (Fin m → ℂ)} (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ))
    (hF : ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) (x : ℂ ⊗[ℤ] O) (i j : Fin g) :
    DifferentiableOn ℂ (fun b => complexExtend (F b) x i j) B := by sorry
