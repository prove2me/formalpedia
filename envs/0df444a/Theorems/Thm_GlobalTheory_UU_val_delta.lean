-- Prove2me | Theorems.Thm_GlobalTheory_UU_val_delta
-- name    : GlobalTheory.UU.val_delta
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:14.880856+00:00
-- url     : https://prove2.me/theorems/5f1121e9-090d-404a-a17d-4114093f9e59
-- title:
--   UU: val delta
-- statement:
--   The UU construction uses the val delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ChainVal.lean#L78-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ChainVal.lean#L78-L99

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

theorem GlobalTheory.UU.val_delta (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by sorry
