-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_toFibre_surjective
-- name    : GlobalTheory.GrpTangent.toFibre_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:59:09.302335+00:00
-- url     : https://prove2.me/theorems/61e51bf2-5527-42d3-ac4c-445660928166
-- title:
--   Grp Tangent: to Fibre surjective
-- statement:
--   The Grp Tangent construction uses the to Fibre surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L480-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L480-L485

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

theorem GlobalTheory.GrpTangent.toFibre_surjective {X : Over S} : Function.Surjective (toFibre p (X := X)) := by sorry
