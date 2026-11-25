-- Prove2me | Theorems.Thm_GlobalTheory_character_mem_lattice_of_comul
-- name    : GlobalTheory.character_mem_lattice_of_comul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:28.549294+00:00
-- url     : https://prove2.me/theorems/340cb764-c0ba-4f70-9f67-6c8f3e546721
-- title:
--   Global Theory: character mem lattice of comul
-- statement:
--   The Global Theory construction uses the character mem lattice of comul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CharacterMemLatticeOfComul.lean#L107-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CharacterMemLatticeOfComul.lean#L107-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CharacterMemLatticeOfComul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.character_mem_lattice_of_comul : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (N : Type) [AddCommMonoid N] [Finite N] (A : Submodule O (N → C)), A.FG → Submodule.span C (A : Set (N → C)) = ⊤ → (∀ f ∈ A, ∃ (m : ℕ) (g h : Fin m → N → C), (∀ i, g i ∈ A) ∧ (∀ i, h i ∈ A) ∧ ∀ x y, f (x + y) = ∑ i, g i x * h i y) → (∀ f ∈ A, ∃ o : O, algebraMap O C o = f 0) → ∀ κ : N → C, κ 0 = 1 → (∀ x y, κ (x + y) = κ x * κ y) → κ ∈ A := by sorry
