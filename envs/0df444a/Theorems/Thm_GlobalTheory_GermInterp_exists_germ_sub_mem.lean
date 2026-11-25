-- Prove2me | Theorems.Thm_GlobalTheory_GermInterp_exists_germ_sub_mem
-- name    : GlobalTheory.GermInterp.exists_germ_sub_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:44.34847+00:00
-- url     : https://prove2.me/theorems/e27c8446-528e-4e5c-b496-2446b8475e8b
-- title:
--   Germ Interp: exists germ sub mem
-- statement:
--   The Germ Interp construction uses the exists germ sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsMaximalOfFinitePrimes.lean#L143-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsMaximalOfFinitePrimes.lean#L143-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsMaximalOfFinitePrimes
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
open GlobalTheory
open GlobalTheory GlobalTheory.GermInterp

theorem GlobalTheory.GermInterp.exists_germ_sub_mem : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (a : ∀ y : X, X.presheaf.stalk y), LocallyOfFiniteType p → IsAffineOpen V → Set.Finite {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)} → ∃ r : Γ(X, V), ∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i)) := by sorry
