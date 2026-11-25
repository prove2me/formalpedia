-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FractionLevelCorrespondence_le_chart
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence.le_chart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:09.251861+00:00
-- url     : https://prove2.me/theorems/7f5d090e-85ae-4ee4-89df-48c4c68ce0db
-- title:
--   Fraction Level Correspondence: le chart
-- statement:
--   The Fraction Level Correspondence construction uses the le chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FractionLevelCorrespondence.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FractionLevelCorrespondence.lean#L37-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FractionLevelCorrespondence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
variable {X X' T : Scheme.{0}} {K : Type} [Fintype K]

theorem GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence.le_chart {L' : LB X'} {L : LB X} {φ : X' ⟶ X} {a : K → (T ⟶ X')} {b : K → (T ⟶ X)}
    {ε : K → ℤ} (hb : ∀ k, b k = a k ≫ φ) {j' : K → L'.ι} {j : K → L.ι} {V : T.Opens}
    (h' : V ≤ (LB.LinComb L' a ε).U j') (h : V ≤ (LB.LinComb L b ε).U j) (k : K) :
    V ≤ a k ⁻¹ᵁ ((L.pull φ).U (fun _ => j k) ⊓ L'.U (j' k)) := by sorry
