-- Prove2me | Theorems.Thm_GlobalTheory_CompRat_exists_real_extension_of_lattice
-- name    : GlobalTheory.CompRat.exists_real_extension_of_lattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:19:52.749602+00:00
-- url     : https://prove2.me/theorems/668d77b8-a5e1-588d-b473-25049a07f2cb
-- title:
--   Comp Rat: exists real extension of lattice
-- statement:
--   The Comp Rat construction uses the exists real extension of lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsComplexLinearOfPureTypes.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsComplexLinearOfPureTypes.lean#L14-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsComplexLinearOfPureTypes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CompRat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

theorem GlobalTheory.CompRat.exists_real_extension_of_lattice {A V W : Type} [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (P : A →+ V) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) (Q : A →+ W) :
    ∃ r : V →ₗ[ℝ] W, ∀ a, r (P a) = Q a := by sorry
