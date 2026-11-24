-- Prove2me | Theorems.Thm_GlobalTheory_QuotientDescent_mem_equivariantSubgroup
-- name    : GlobalTheory.QuotientDescent.mem_equivariantSubgroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:15.504809+00:00
-- url     : https://prove2.me/theorems/612a09c7-cd23-4bee-b701-1fd28abfb7b9
-- title:
--   Quotient Descent: mem equivariant Subgroup
-- statement:
--   The Quotient Descent construction uses the mem equivariant Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/QuotientDescendGrpObj.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/QuotientDescendGrpObj.lean#L85-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientDescent
variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}
variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}
omit [Finite Γ]

theorem GlobalTheory.QuotientDescent.mem_equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).hom (τ g).hom)
    {T : Over X'} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariantSubgroup hτ T ↔ Equivariant ρ τ w := by sorry
