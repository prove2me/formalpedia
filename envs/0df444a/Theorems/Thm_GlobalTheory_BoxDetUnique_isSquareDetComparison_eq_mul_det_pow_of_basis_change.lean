-- Prove2me | Theorems.Thm_GlobalTheory_BoxDetUnique_isSquareDetComparison_eq_mul_det_pow_of_basis_change
-- name    : GlobalTheory.BoxDetUnique.isSquareDetComparison_eq_mul_det_pow_of_basis_change
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:04:27.266165+00:00
-- url     : https://prove2.me/theorems/1cae1c76-9db8-4c19-83dc-17ea61574732
-- title:
--   Box Det Unique: is Square Det Comparison eq mul det pow of basis change
-- statement:
--   The Box Det Unique construction uses the is Square Det Comparison eq mul det pow of basis change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsSquareDetComparisonEqMulDetPowOfBasisChange.lean#L74-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsSquareDetComparisonEqMulDetPowOfBasisChange.lean#L74-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonEqMulDetPowOfBasisChange
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
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique

theorem GlobalTheory.BoxDetUnique.isSquareDetComparison_eq_mul_det_pow_of_basis_change : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b b' : Fin (m ^ x.P.g) → RR x m) (B : (Matrix (Fin (m ^ x.P.g)) (Fin (m ^ x.P.g)) K)ˣ) (lam lam' : Kˣ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ k, Coords x b (fun k' => B.val k' k) (b' k).f) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x m al b' lam' → lam' = lam * (Matrix.GeneralLinearGroup.det B) ^ (-8 * (m ^ (3 * x.P.g + 2) : ℕ) : ℤ) := by sorry
