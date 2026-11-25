-- Prove2me | Theorems.Thm_GlobalTheory_const_of_finite_family_spAct
-- name    : GlobalTheory.const_of_finite_family_spAct
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:41.463389+00:00
-- url     : https://prove2.me/theorems/0660040f-b6d7-43b8-b99a-52a6684f83dd
-- title:
--   Global Theory: const of finite family sp Act
-- statement:
--   The Global Theory construction uses the const of finite family sp Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ProdCompEqOfFiniteFamily.lean#L45-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ProdCompEqOfFiniteFamily.lean#L45-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ProdCompEqOfFiniteFamily
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
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory

theorem GlobalTheory.const_of_finite_family_spAct :
    Key.PhHoloStatement → ∀ (g : ℕ) (I : Type) [Finite I] (F : I → Matrix (Fin g) (Fin g) ℂ → ℂ), 2 ≤ g → (∀ i, Key.IsHoloSiegel g (F i)) → (∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = F j (Key.Chi.spAct sp τ)) → ∀ i, ∃ c, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = c := by sorry
