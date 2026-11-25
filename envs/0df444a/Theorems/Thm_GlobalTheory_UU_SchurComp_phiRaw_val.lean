-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_phiRaw_val
-- name    : GlobalTheory.UU.SchurComp.phiRaw_val
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:44.56038+00:00
-- url     : https://prove2.me/theorems/93114f5e-6ac1-4aac-8a31-0a54fe6dd6fe
-- title:
--   Schur Comp: phi Raw val
-- statement:
--   The Schur Comp construction uses the phi Raw val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean#L91-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UU.SchurComp.phiRaw_val {k : ℕ} {g : GtPtF D F}
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') {α : D.X}
    {u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))} (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval (s' α) r z J = sval (s α) (r ≫ (DegPre.trPt D F g.b).left) z J * (val u r z J).val := by sorry
