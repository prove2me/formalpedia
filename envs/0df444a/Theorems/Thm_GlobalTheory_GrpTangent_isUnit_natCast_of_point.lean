-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_isUnit_natCast_of_point
-- name    : GlobalTheory.GrpTangent.isUnit_natCast_of_point
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:59:10.068806+00:00
-- url     : https://prove2.me/theorems/75c53836-96b3-4ff6-8b22-0b830acc8d33
-- title:
--   Grp Tangent: is Unit nat Cast of point
-- statement:
--   The Grp Tangent construction uses the is Unit nat Cast of point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L609-L611
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L609-L611

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
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem GlobalTheory.GrpTangent.isUnit_natCast_of_point {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {R : Type} [CommRing R]
    (p : Sp R ⟶ S) : IsUnit (n : R) := by sorry
