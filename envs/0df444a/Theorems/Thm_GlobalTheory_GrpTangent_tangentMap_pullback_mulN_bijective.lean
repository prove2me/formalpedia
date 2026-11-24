-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_tangentMap_pullback_mulN_bijective
-- name    : GlobalTheory.GrpTangent.tangentMap_pullback_mulN_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:32.953289+00:00
-- url     : https://prove2.me/theorems/1de5a5fb-6903-4e58-8c1e-23d78e1acd4f
-- title:
--   Grp Tangent: tangent Map pullback mul N bijective
-- statement:
--   The Grp Tangent construction uses the tangent Map pullback mul N bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L613-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L613-L617

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

theorem GlobalTheory.GrpTangent.tangentMap_pullback_mulN_bijective [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    {R : Type} [CommRing R] (p : Sp R ⟶ S) :
    Function.Bijective (tangentMap ((Over.pullback p).map (mulN G n))) := by sorry
