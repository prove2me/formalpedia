-- Prove2me | Theorems.Thm_GlobalTheory_PrimCocycle_primitive_cocycle
-- name    : GlobalTheory.PrimCocycle.primitive_cocycle
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:40.788833+00:00
-- url     : https://prove2.me/theorems/4a04c8b3-113d-4b4b-b47f-6803222808c7
-- title:
--   Prim Cocycle: primitive cocycle
-- statement:
--   The Prim Cocycle construction uses the primitive cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean#L97-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean#L97-L129

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem GlobalTheory.PrimCocycle.primitive_cocycle : GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (O : RigLB B), (∃ t : LB.Gen (abelian₂ B O.L), t.IsGen) → ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen ∧ ∀ (Z : Over S) (z : Z.left) (J : (Z.left ⟶ B.left) → O.L.ι), Geo.Tor.Good O.L z J → let v : (Z ⟶ B) → (Z ⟶ B) → (Z.left.presheaf.stalk z)ˣ := fun x y => Geo.Tor.val (L := O.L) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (ε := fun I => (-1) ^ (2 - I.down.card)) t (lift x y).left z J; (∀ x, v x 1 = 1) ∧ (∀ x y, v x y = v y x) ∧ ∀ x y w, v (x * y) w * v x y = v x (y * w) * v y w := by sorry
