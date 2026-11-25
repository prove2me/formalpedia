-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_jac_eq_unit_mul_det_pderiv
-- name    : GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:34.764853+00:00
-- url     : https://prove2.me/theorems/79019a31-c680-4281-a856-b20f1a46eab5
-- title:
--   Key Ka: jac eq unit mul det pderiv
-- statement:
--   The Key Ka construction uses the jac eq unit mul det pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacEqUnitMulDetPderiv.lean#L154-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacEqUnitMulDetPderiv.lean#L154-L200

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
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (θ : Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left) (z : Pt x) (e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] O), θ ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O)) → (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) θ V (t i) = MvPowerSeries.X i) → (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ x.P.A.left), w ≫ x.P.A.hom = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) → ∃ e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) → (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → spMap e.toRingHom ≫ θ = z.left → ∃ u : Oˣ, ∀ (n : ℕ) (s : Fin x.P.g → RR x n) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → jac x s z c = u * e (Matrix.of fun i j => MvPowerSeries.pderiv O j (valT (T := (MvPowerSeries (Fin x.P.g) O)) θ (x.P.L.U c) ((s i).f c))).det := by sorry
