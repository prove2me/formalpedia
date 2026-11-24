-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_eq_of_tangentMap_injective
-- name    : GlobalTheory.GrpTangent.eq_of_tangentMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:34.069798+00:00
-- url     : https://prove2.me/theorems/bbb4099d-6917-44a0-8a7b-1515e341b01f
-- title:
--   Grp Tangent: eq of tangent Map injective
-- statement:
--   The Grp Tangent construction uses the eq of tangent Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L536-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L536-L545

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

theorem GlobalTheory.GrpTangent.eq_of_tangentMap_injective
    (h : Function.Injective (tangentMap ((Over.pullback p).map f)))
    (w w' : Over.mk (dualBase k ≫ p) ⟶ G) (h₀ : epsZeroAt p ≫ w = epsZeroAt p ≫ w')
    (hf : w ≫ f = w' ≫ f) : w = w' := by sorry
