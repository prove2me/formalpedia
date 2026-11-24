-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_exists_normalised_mulPull
-- name    : GlobalTheory.KeyKa.exists_normalised_mulPull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:15.353071+00:00
-- url     : https://prove2.me/theorems/6d514a02-76a2-4321-ac35-999d29d2b473
-- title:
--   Key Ka: exists normalised mul Pull
-- statement:
--   The Key Ka construction uses the exists normalised mul Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNormalisedIsoPullbackMulByM.lean#L31-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNormalisedIsoPullbackMulByM.lean#L31-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisedIsoPullbackMulByM
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
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.exists_normalised_mulPull : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ), ∃ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen ∧ ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) := by sorry
