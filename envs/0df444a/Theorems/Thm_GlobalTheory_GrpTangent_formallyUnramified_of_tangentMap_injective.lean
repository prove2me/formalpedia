-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_formallyUnramified_of_tangentMap_injective
-- name    : GlobalTheory.GrpTangent.formallyUnramified_of_tangentMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:06.801807+00:00
-- url     : https://prove2.me/theorems/5e8b043c-34fa-4ddd-9630-55e1319f9577
-- title:
--   Grp Tangent: formally Unramified of tangent Map injective
-- statement:
--   The Grp Tangent construction uses the formally Unramified of tangent Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L549-L562
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L549-L562

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

theorem GlobalTheory.GrpTangent.formallyUnramified_of_tangentMap_injective (f : G ⟶ H) [IsMonHom f]
    [LocallyOfFiniteType f.left]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Injective (tangentMap ((Over.pullback p).map f))) :
    FormallyUnramified f.left := by sorry
