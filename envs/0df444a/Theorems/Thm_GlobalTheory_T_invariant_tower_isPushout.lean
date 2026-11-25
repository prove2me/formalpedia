-- Prove2me | Theorems.Thm_GlobalTheory_T_invariant_tower_isPushout
-- name    : GlobalTheory.T.invariant_tower_isPushout
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:09.722905+00:00
-- url     : https://prove2.me/theorems/1753963c-8535-4972-a49b-ac096ce485b5
-- title:
--   T: invariant tower is Pushout
-- statement:
--   The T construction uses the invariant tower is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantTowerAlgebraMapInjectiveStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantTowerAlgebraMapInjectiveStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjectiveStatement
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

theorem GlobalTheory.T.invariant_tower_isPushout : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by sorry
