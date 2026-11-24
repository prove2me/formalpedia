-- Prove2me | Theorems.Thm_GlobalTheory_T_keyInvariantFromIntersection_unique
-- name    : GlobalTheory.T.keyInvariantFromIntersection_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:11.740247+00:00
-- url     : https://prove2.me/theorems/1f759845-64fc-43c4-b3bd-47e2838c5152
-- title:
--   T: key Invariant From Intersection unique
-- statement:
--   The T construction uses the key Invariant From Intersection unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KeyInvariantFromIntersectionUniqueStatement.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KeyInvariantFromIntersectionUniqueStatement.lean#L18-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KeyInvariantFromIntersectionUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KeyInvariantFromIntersectionUniqueStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.keyInvariantFromIntersection_unique : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by sorry
