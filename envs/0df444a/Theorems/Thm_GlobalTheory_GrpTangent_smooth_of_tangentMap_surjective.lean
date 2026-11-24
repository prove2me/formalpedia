-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_smooth_of_tangentMap_surjective
-- name    : GlobalTheory.GrpTangent.smooth_of_tangentMap_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:19.752581+00:00
-- url     : https://prove2.me/theorems/425cd7e4-b763-4de4-837e-3f9cdcc684f6
-- title:
--   Grp Tangent: smooth of tangent Map surjective
-- statement:
--   The Grp Tangent construction uses the smooth of tangent Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L564-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L564-L574

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

theorem GlobalTheory.GrpTangent.smooth_of_tangentMap_surjective (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Surjective (tangentMap ((Over.pullback p).map f))) :
    Smooth f.left := by sorry
