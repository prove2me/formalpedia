-- Prove2me | Theorems.Thm_GlobalTheory_JacGen_exists_derivations
-- name    : GlobalTheory.JacGen.exists_derivations
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:34.381585+00:00
-- url     : https://prove2.me/theorems/3fa0e4d5-b2e2-45f1-9f7c-a10489abd45c
-- title:
--   Jac Gen: exists derivations
-- statement:
--   The Jac Gen construction uses the exists derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacNeZeroIffSpanEqMaximalIdeal.lean#L119-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacNeZeroIffSpanEqMaximalIdeal.lean#L119-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}
variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}

theorem GlobalTheory.JacGen.exists_derivations (hv : IsLieBasis v) {S : Type} [CommRing S] [Algebra K S] (j : sp (R₀ := K) S ⟶ G)
    [Mono j] (z : 𝟙_ _ ⟶ G) (u : S →ₐ[K] K) (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : S →ₐ[K] TrivSqZeroExt K (Fin n → K))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ D : Fin n → S →ₗ[K] K, (∀ k a b, D k (a * b) = u a * D k b + u b * D k a) ∧
      (∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0) ∧
      (∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k) ∧
      ∀ k, ∃ φ : S →ₐ[K] DualNumber K, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧ ∀ a, (φ a).snd = D k a := by sorry
