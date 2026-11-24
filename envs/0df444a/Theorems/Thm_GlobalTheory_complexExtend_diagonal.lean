-- Prove2me | Theorems.Thm_GlobalTheory_complexExtend_diagonal
-- name    : GlobalTheory.complexExtend_diagonal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:41.007872+00:00
-- url     : https://prove2.me/theorems/ad9470a6-946f-4092-9b78-ab3099e5a9b9
-- title:
--   Global Theory: complex Extend diagonal
-- statement:
--   The Global Theory construction uses the complex Extend diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnComplexExtend.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnComplexExtend.lean#L42-L54

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

theorem GlobalTheory.complexExtend_diagonal {O : Type} [CommRing O] {g : ℕ}
    (f : O →+* Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (O →+* ℂ))
    (hf : ∀ a, f a = Matrix.diagonal (fun i => ty i a)) (x : ℂ ⊗[ℤ] O) :
    complexExtend f x = Matrix.diagonal (fun i => complexExtend (ty i) x) := by sorry
