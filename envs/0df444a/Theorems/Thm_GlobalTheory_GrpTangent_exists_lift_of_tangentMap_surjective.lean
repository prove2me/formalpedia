-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_exists_lift_of_tangentMap_surjective
-- name    : GlobalTheory.GrpTangent.exists_lift_of_tangentMap_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:56.497051+00:00
-- url     : https://prove2.me/theorems/b84d8027-61b8-4d5c-a63e-4032f500e9d4
-- title:
--   Grp Tangent: exists lift of tangent Map surjective
-- statement:
--   The Grp Tangent construction uses the exists lift of tangent Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L523-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L523-L534

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
variable (f : G ⟶ H) [IsMonHom f]

theorem GlobalTheory.GrpTangent.exists_lift_of_tangentMap_surjective
    (h : Function.Surjective (tangentMap ((Over.pullback p).map f))) (x : Over.mk p ⟶ G)
    (v : Over.mk (dualBase k ≫ p) ⟶ H) (hv : epsZeroAt p ≫ v = x ≫ f) :
    ∃ w : Over.mk (dualBase k ≫ p) ⟶ G, epsZeroAt p ≫ w = x ∧ w ≫ f = v := by sorry
