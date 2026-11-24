-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_toFibre_comp
-- name    : GlobalTheory.GrpTangent.toFibre_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:21.463798+00:00
-- url     : https://prove2.me/theorems/50b0dde9-9e69-4339-9d4b-7c269e0ba0b3
-- title:
--   Grp Tangent: to Fibre comp
-- statement:
--   The Grp Tangent construction uses the to Fibre comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L487-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L487-L493

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
variable {k : Type} [CommRing k] (p : Sp k ⟶ S)

theorem GlobalTheory.GrpTangent.toFibre_comp {X Y : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) (f : X ⟶ Y) :
    toFibre p (w ≫ f) = toFibre p w ≫ (Over.pullback p).map f := by sorry
