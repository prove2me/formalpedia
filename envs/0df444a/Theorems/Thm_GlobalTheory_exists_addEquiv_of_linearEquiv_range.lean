-- Prove2me | Theorems.Thm_GlobalTheory_exists_addEquiv_of_linearEquiv_range
-- name    : GlobalTheory.exists_addEquiv_of_linearEquiv_range
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:53.644896+00:00
-- url     : https://prove2.me/theorems/f5d59201-ed66-526a-8d99-f9b1a06cd13f
-- title:
--   Global Theory: exists add Equiv of linear Equiv range
-- statement:
--   The Global Theory construction uses the exists add Equiv of linear Equiv range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLatticeAutOfIsomorphicThetaObjects.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLatticeAutOfIsomorphicThetaObjects.lean#L36-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLatticeAutOfIsomorphicThetaObjects
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

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
open GlobalTheory

theorem GlobalTheory.exists_addEquiv_of_linearEquiv_range {La : Type} [AddCommGroup La] {g : ℕ} (Q Q' : La →+ (Fin g → ℂ))
    (hQ : Function.Injective Q) (hQ' : Function.Injective Q') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h₁ : ∀ x, h (Q' x) ∈ Q.range) (h₂ : ∀ x, h.symm (Q x) ∈ Q'.range) :
    ∃ gam : La ≃+ La, ∀ x, h (Q' x) = Q (gam x) := by sorry
