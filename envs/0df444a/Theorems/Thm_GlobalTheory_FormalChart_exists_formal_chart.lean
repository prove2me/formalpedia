-- Prove2me | Theorems.Thm_GlobalTheory_FormalChart_exists_formal_chart
-- name    : GlobalTheory.FormalChart.exists_formal_chart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:27.270625+00:00
-- url     : https://prove2.me/theorems/9a74fcb8-651a-44a5-ab0d-9fe32c71b2dc
-- title:
--   Formal Chart: exists formal chart
-- statement:
--   The Formal Chart construction uses the exists formal chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LePreimageOfClosedPoint.lean#L162-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LePreimageOfClosedPoint.lean#L162-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.FormalChart
open GlobalTheory.KeyKa.EtBaseChange

theorem GlobalTheory.FormalChart.exists_formal_chart : ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0}) (h : X ⟶ Sp O) (g : ℕ) (z : Sp O ⟶ X), SmoothOfRelativeDimension g h → z ≫ h = 𝟙 _ → ∃ θ : Sp (MvPowerSeries (Fin g) O) ⟶ X, θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) = z (IsLocalRing.closedPoint O) ∧ θ ≫ h = spMap (algebraMap O (MvPowerSeries (Fin g) O)) ∧ (∃ (V : X.Opens) (t : Fin g → Γ(X, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin g) O)) θ V (t i) = MvPowerSeries.X i) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ X), w ≫ h = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) → ∃ e : (MvPowerSeries (Fin g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) := by sorry
