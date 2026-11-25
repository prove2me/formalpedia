-- Prove2me | Theorems.Thm_GlobalTheory_TauDescent_tauBimult_down
-- name    : GlobalTheory.TauDescent.tauBimult_down
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:44.632807+00:00
-- url     : https://prove2.me/theorems/fd39f76c-95f5-4869-b999-8469b2e5f7de
-- title:
--   Tau Descent: tau Bimult down
-- statement:
--   The Tau Descent construction uses the tau Bimult down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TauBimultOfBaseChange.lean#L74-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TauBimultOfBaseChange.lean#L74-L153

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TauBimultOfBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory
open GlobalTheory.TauDescent
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {β : D'.P.A.left ⟶ D.P.A.left}
set_option maxHeartbeats 1000000

theorem GlobalTheory.TauDescent.tauBimult_down (hG : GlobalFnsSt) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X)
    (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hvg : v.IsGen)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hρ : RigCmp φ D D' β v)
    (gam : (TK R').left ⟶ (TK R).left) (hgam : gam ≫ jK R = jK R' ≫ spMap φ) (hψ : PsiCmp D D' β v xe gam)
    (hB : D'.TauBimult) : D.TauBimult := by sorry
