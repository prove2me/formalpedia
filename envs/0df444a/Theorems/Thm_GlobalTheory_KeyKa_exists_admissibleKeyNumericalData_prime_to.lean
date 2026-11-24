-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_exists_admissibleKeyNumericalData_prime_to
-- name    : GlobalTheory.KeyKa.exists_admissibleKeyNumericalData_prime_to
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:53.668576+00:00
-- url     : https://prove2.me/theorems/fdf5ef71-095e-4439-bfe9-a92d53f37ed0
-- title:
--   Key Ka: exists admissible Key Numerical Data prime to
-- statement:
--   The Key Ka construction uses the exists admissible Key Numerical Data prime to property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAdmissibleKeyNumericalDataPrimeTo.lean#L29-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAdmissibleKeyNumericalDataPrimeTo.lean#L29-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAdmissibleKeyNumericalDataPrimeTo
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
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.exists_admissibleKeyNumericalData_prime_to : ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted g n l l' al ∧ ¬ p ∣ degProd g n l l' ∧ 1 ≤ degProd g n l l' ∧ 1 ≤ kaExp g n l l' := by sorry
