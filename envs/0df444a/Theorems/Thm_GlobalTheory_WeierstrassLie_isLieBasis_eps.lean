-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassLie_isLieBasis_eps
-- name    : GlobalTheory.WeierstrassLie.isLieBasis_eps
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:58.620374+00:00
-- url     : https://prove2.me/theorems/de0cac81-e9db-511c-90cb-cec10889308c
-- title:
--   Weierstrass Lie: is Lie Basis eps
-- statement:
--   The Weierstrass Lie construction uses the is Lie Basis eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveFst.lean#L103-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveFst.lean#L103-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
noncomputable section
open GlobalTheory GlobalTheory.WeierstrassLie
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem GlobalTheory.WeierstrassLie.isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R)
    [GrpObj (schemeOver W)], η[schemeOver W].left = zero W → ∃ v : epsR R ⟶ schemeOver W,
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by sorry
