-- Prove2me | Theorems.Thm_GlobalTheory_TauPull_tauW_mul
-- name    : GlobalTheory.TauPull.tauW_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:03:18.138633+00:00
-- url     : https://prove2.me/theorems/d373b39e-49c2-4d9b-8fda-c893336d74cd
-- title:
--   Tau Pull: tau W mul
-- statement:
--   The Tau Pull construction uses the tau W mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultOfIsPullDeg.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultOfIsPullDeg.lean#L127-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem GlobalTheory.TauPull.tauW_mul (hB : D.TauBimult) (ψW : PsiOn D W) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W)
    {z : T.left} {J} (hJ : Good D.P.L z J) (a a' b : D.X) :
    val (ψW.tau (a + a') b) κ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (ψW.tau a b) κ.left z J * val (ψW.tau a' b) κ.left z J := by sorry
