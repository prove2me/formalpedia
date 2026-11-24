-- Prove2me | Theorems.Thm_GlobalTheory_isPushout_of_tame
-- name    : GlobalTheory.isPushout_of_tame
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:17.229872+00:00
-- url     : https://prove2.me/theorems/5ca5147a-3b3f-4a3b-9ea0-78b94273be31
-- title:
--   Global Theory: is Pushout of tame
-- statement:
--   The Global Theory construction uses the is Pushout of tame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantTowerAlgebraMapInjective.lean#L62-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantTowerAlgebraMapInjective.lean#L62-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulMemSpanInvariantsSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubalgebraEqTopOfForallPrimeSmulMemSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjective
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

theorem GlobalTheory.isPushout_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by sorry
