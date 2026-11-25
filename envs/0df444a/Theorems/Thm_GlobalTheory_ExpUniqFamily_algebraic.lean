-- Prove2me | Theorems.Thm_GlobalTheory_ExpUniqFamily_algebraic
-- name    : GlobalTheory.ExpUniqFamily.algebraic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:00.236159+00:00
-- url     : https://prove2.me/theorems/93fdb9cf-8492-4093-a831-8a1368580b5b
-- title:
--   Exp Uniq Family: algebraic
-- statement:
--   The Exp Uniq Family construction uses the algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FamilyUnifExpUnique.lean#L52-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FamilyUnifExpUnique.lean#L52-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.ExpUniqFamily

theorem GlobalTheory.ExpUniqFamily.algebraic {O Q L L' : Type} [CommRing O] [Group Q] [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {g : ℕ} (χ : Fin g → O → ℂ) (P : L →+ (Fin g → ℂ)) (P' : L' →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x i, P (a • x) i = χ i a * P x i) (hP' : ∀ (a : O) x i, P' (a • x) i = χ i a * P' x i)
    (iP : Function.Injective P) (iP' : Function.Injective P')
    (dP : DiscreteTopology P.range) (dP' : DiscreteTopology P'.range)
    (e e' : (Fin g → ℂ) → Q) (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (act : O → Q → Q) (hl : ∀ a z, e (fun k => χ k a * z k) = act a (e z))
    (hl' : ∀ a z, e' (fun k => χ k a * z k) = act a (e' z))
    (f f' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, e' (f z) = e z) (hf' : ∀ z, e (f' z) = e' z) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L ≃ₗ[O] L'), (∀ z, e' (h z) = e z) ∧
      (∀ a, P' (gam a) = h (P a)) ∧
      ∀ (k : ℕ) a b, 0 < k → e ((k : ℂ)⁻¹ • P a) = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by sorry
