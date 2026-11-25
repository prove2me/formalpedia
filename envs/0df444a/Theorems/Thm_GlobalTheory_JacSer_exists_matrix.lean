-- Prove2me | Theorems.Thm_GlobalTheory_JacSer_exists_matrix
-- name    : GlobalTheory.JacSer.exists_matrix
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:44.717556+00:00
-- url     : https://prove2.me/theorems/6eef9692-1ed2-4579-828e-8c219800e164
-- title:
--   Jac Ser: exists matrix
-- statement:
--   The Jac Ser construction uses the exists matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacEqUnitMulDetPderiv.lean#L95-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacEqUnitMulDetPderiv.lean#L95-L141

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacEqUnitMulDetPderiv
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
open GlobalTheory GlobalTheory.JacSer
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR O ⟶ G)}

theorem GlobalTheory.JacSer.exists_matrix (hv : IsLieBasis v) (j : sp (R₀ := O) (MvPowerSeries (Fin n) O) ⟶ G)
    (inj : ∀ {T : Type} [CommRing T] [Algebra O T] (φ ψ : MvPowerSeries (Fin n) O →ₐ[O] T),
      spMap φ ≫ j = spMap ψ ≫ j → ∀ i, φ (X i) = ψ (X i))
    (z : 𝟙_ _ ⟶ G) (u : MvPowerSeries (Fin n) O →ₐ[O] O) (hu0 : ∀ i, u (X i) ∈ maximalIdeal O)
    (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : MvPowerSeries (Fin n) O →ₐ[O] TrivSqZeroExt O (Fin n → O))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ C : Matrix (Fin n) (Fin n) O, IsUnit C.det ∧
      ∀ k, ∃ φ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧
        ∀ a, (φ a).snd = ∑ i, u (pderiv O i a) * C i k := by sorry
