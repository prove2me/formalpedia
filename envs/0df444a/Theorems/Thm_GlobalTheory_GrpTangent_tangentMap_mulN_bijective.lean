-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_tangentMap_mulN_bijective
-- name    : GlobalTheory.GrpTangent.tangentMap_mulN_bijective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:59:08.850907+00:00
-- url     : https://prove2.me/theorems/4c9752d1-8fbf-4820-b2f7-1f951c1a68e7
-- title:
--   Grp Tangent: tangent Map mul N bijective
-- statement:
--   The Grp Tangent construction uses the tangent Map mul N bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L594-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L594-L605

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

theorem GlobalTheory.GrpTangent.tangentMap_mulN_bijective {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : R)) : Function.Bijective (tangentMap (mulN G n)) := by sorry
