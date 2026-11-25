-- Prove2me | Theorems.Thm_GlobalTheory_RosatiCube_rosati_cubical_additive
-- name    : GlobalTheory.RosatiCube.rosati_cubical_additive
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:52.177797+00:00
-- url     : https://prove2.me/theorems/da4b462b-d385-4883-ba2e-ac5bbdf34a7c
-- title:
--   Rosati Cube: rosati cubical additive
-- statement:
--   The Rosati Cube construction uses the rosati cubical additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L167-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L167-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RosatiCube
open ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : LB A.left}
variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem GlobalTheory.RosatiCube.rosati_cubical_additive : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ (a : O) (x x' y : T ⟶ G), val₂ (u a) z J (x * x') y * cubV c z J x x' (y ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) (x' ≫ act.act a) y * (val₂ (u a) z J x y * val₂ (u a) z J x' y)) ∧ (∀ (a : O) (x y y' : T ⟶ G), val₂ (u a) z J x (y * y') * cubV c z J x (y ≫ act.act (star a)) (y' ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) y y' * (val₂ (u a) z J x y * val₂ (u a) z J x y')) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a + b)) z J x y * cubV c z J x (y ≫ act.act (star a)) (y ≫ act.act (star b)) = cubV c z J (x ≫ act.act a) (x ≫ act.act b) y * (val₂ (u a) z J x y * val₂ (u b) z J x y)) := by sorry
