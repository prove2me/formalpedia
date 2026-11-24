-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_epsScale_add_comp
-- name    : GlobalTheory.GrpTangent.epsScale_add_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:16.279805+00:00
-- url     : https://prove2.me/theorems/c1422137-6c76-462e-b14c-c414089ba2d3
-- title:
--   Grp Tangent: eps Scale add comp
-- statement:
--   The Grp Tangent construction uses the eps Scale add comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L395-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L395-L425

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
variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]

theorem GlobalTheory.GrpTangent.epsScale_add_comp (a b : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    epsScale (a + b) ≫ w = (epsScale a ≫ w) * (epsScale b ≫ w) := by sorry
