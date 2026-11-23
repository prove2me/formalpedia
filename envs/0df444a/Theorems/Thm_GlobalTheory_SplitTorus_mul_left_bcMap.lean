-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorus_mul_left_bcMap
-- name    : GlobalTheory.SplitTorus.mul_left_bcMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:59:29.798412+00:00
-- url     : https://prove2.me/theorems/06b8bbc0-1709-4786-a495-8905218ac2b3
-- title:
--   Split Torus: mul left bc Map
-- statement:
--   The Split Torus construction uses the mul left bc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L669-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L669-L675

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S S' : Scheme.{u}} (f : S' ⟶ S) (X Y : Type u) [AddCommGroup X] [AddCommGroup Y]

theorem GlobalTheory.SplitTorus.mul_left_bcMap (T : Over S') (x y : T ⟶ splitTorus S' X)
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X) (hx : x₀.left = x.left ≫ bcMap f X)
    (hy : y₀.left = y.left ≫ bcMap f X) : (x₀ * y₀).left = (x * y).left ≫ bcMap f X := by sorry
