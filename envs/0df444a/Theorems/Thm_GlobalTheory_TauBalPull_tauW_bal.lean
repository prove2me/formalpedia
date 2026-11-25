-- Prove2me | Theorems.Thm_GlobalTheory_TauBalPull_tauW_bal
-- name    : GlobalTheory.TauBalPull.tauW_bal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:03:33.344345+00:00
-- url     : https://prove2.me/theorems/2bd59b4c-f8b6-4936-ad46-273d60613061
-- title:
--   Tau Bal Pull: tau W bal
-- statement:
--   The Tau Bal Pull construction uses the tau W bal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L71-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
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
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem GlobalTheory.TauBalPull.tauW_bal (ψW : PsiOn D W)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b'))
    {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau a b) κ.left z J * val₂ u z J (cP D T y) (cP D T y') = val (ψW.tau a' b') κ.left z J := by sorry
