-- Prove2me | Theorems.Thm_GlobalTheory_PsiWZeroPull_rel_on
-- name    : GlobalTheory.PsiWZeroPull.rel_on
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:24.207419+00:00
-- url     : https://prove2.me/theorems/19ebbe24-a2ae-45ce-9103-5c2dbb10a50a
-- title:
--   Psi WZero Pull: rel on
-- statement:
--   The Psi WZero Pull construction uses the rel on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TraceFormTwistIsoOfPullback.lean#L26-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TraceFormTwistIsoOfPullback.lean#L26-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TraceFormTwistIsoOfPullback
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
open GlobalTheory.PsiWZeroPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem GlobalTheory.PsiWZeroPull.rel_on (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty) {K : Type} [Fintype K]
    {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.xK a)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi a) D.rigK)) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (LB.pullGen D.P.L _ _ u (cP D (TW W) a).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi a) (D.rigW W)) := by sorry
