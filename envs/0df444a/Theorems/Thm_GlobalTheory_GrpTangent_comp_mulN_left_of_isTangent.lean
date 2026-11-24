-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_comp_mulN_left_of_isTangent
-- name    : GlobalTheory.GrpTangent.comp_mulN_left_of_isTangent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:51.679279+00:00
-- url     : https://prove2.me/theorems/4013576e-d73f-493b-a890-5a85c8d4519a
-- title:
--   Grp Tangent: comp mul N left of is Tangent
-- statement:
--   The Grp Tangent construction uses the comp mul N left of is Tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L589-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L589-L592

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

theorem GlobalTheory.GrpTangent.comp_mulN_left_of_isTangent {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
    {w : epsR R ⟶ G} (hw : IsTangent w) (n : ℕ) :
    (w ≫ mulN G n).left = spMap (epsScaleR (n : R)) ≫ w.left := by sorry
