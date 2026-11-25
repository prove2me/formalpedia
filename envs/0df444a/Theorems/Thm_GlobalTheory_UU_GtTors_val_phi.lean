-- Prove2me | Theorems.Thm_GlobalTheory_UU_GtTors_val_phi
-- name    : GlobalTheory.UU.GtTors.val_phi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:29.472652+00:00
-- url     : https://prove2.me/theorems/6be27710-6acb-595e-ad66-60ae86f7c55b
-- title:
--   Gt Tors: val phi
-- statement:
--   The Gt Tors construction uses the val phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ChainVal.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ChainVal.lean#L62-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
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
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UU.GtTors.val_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (ρ ≫ fst _ _).left z J := by sorry
