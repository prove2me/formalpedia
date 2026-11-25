-- Prove2me | Theorems.Thm_GlobalTheory_ConvOfProd_main
-- name    : GlobalTheory.ConvOfProd.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:43:11.738443+00:00
-- url     : https://prove2.me/theorems/9dcfa83c-e8fc-44c5-bb4c-b3bd7b777f1e
-- title:
--   Conv Of Prod: main
-- statement:
--   The Conv Of Prod construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSubSum.lean#L85-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSubSum.lean#L85-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSubSum
import Theorems.Thm_GlobalTheory_LiftTest_main

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
open GlobalTheory GlobalTheory.ConvOfProd
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.ConvOfProd.main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (f : ∀ α, SecBT D T k α) (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) (σ : U.SecGT T (k + l)), U.ProdExp T f g σ → U.ExpT T (k + l) σ h → ConvT I f g h := by sorry
