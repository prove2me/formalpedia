-- Prove2me | Theorems.Thm_GlobalTheory_semiAbelian_torsion_finite_and_closedPoint_finiteOrder
-- name    : GlobalTheory.semiAbelian_torsion_finite_and_closedPoint_finiteOrder
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:06.740853+00:00
-- url     : https://prove2.me/theorems/bf1d91ec-01f5-4c4b-b2d7-87440e73f479
-- title:
--   Global Theory: semi Abelian torsion finite and closed Point finite Order
-- statement:
--   The Global Theory construction uses the semi Abelian torsion finite and closed Point finite Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L115-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L115-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open SemiAbTorsion

theorem GlobalTheory.semiAbelian_torsion_finite_and_closedPoint_finiteOrder : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → (∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1}) ∧ (∀ (Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (w : G.left), IsClosed ({w} : Set G.left) → ∃ n : ℕ, 1 ≤ n ∧ ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G), Set.range x.left = {w} → x ^ n = 1) := by sorry
