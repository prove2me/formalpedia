-- Prove2me | Theorems.Thm_GlobalTheory_KeyVia_main
-- name    : GlobalTheory.KeyVia.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:02.038817+00:00
-- url     : https://prove2.me/theorems/21c333d6-cdc1-45ea-89e0-b7188d04222d
-- title:
--   Key Via: main
-- statement:
--   The Key Via construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PwIsoIsGen.lean#L118-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PwIsoIsGen.lean#L118-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
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
open GlobalTheory GlobalTheory.KeyVia
variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

theorem GlobalTheory.KeyVia.main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R'), (KeyPB x' x f ↔ ∃ φ w, KeyVia x' x f φ w) ∧ ∀ φ w, KeyVia x' x f φ w → (∀ (l : ℕ) (s : RR x l), ∃! s' : RR x' l, SecVia x' x φ w s' s) ∧ (∀ z : Pt x, ∃! z' : Pt x', z'.left ≫ φ = spMap f ≫ z.left) ∧ ∀ (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l) (s : RR x l) (s' : RR x' l) (c : Fin N → R), (∀ k, SecVia x' x φ w (b' k) (b k)) → SecVia x' x φ w s' s → Coords x b c s.f → Coords x' b' (fun k => f (c k)) s'.f := by sorry
