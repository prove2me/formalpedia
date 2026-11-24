-- Prove2me | Theorems.Thm_GlobalTheory_TauPull_tauW_corr
-- name    : GlobalTheory.TauPull.tauW_corr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:03:36.160365+00:00
-- url     : https://prove2.me/theorems/b70efd97-e027-49e5-884e-ea7e6d8ce54b
-- title:
--   Tau Pull: tau W corr
-- statement:
--   The Tau Pull construction uses the tau W corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultOfIsPullDeg.lean#L83-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultOfIsPullDeg.lean#L83-L125

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

theorem GlobalTheory.TauPull.tauW_corr (hB : D.TauBimult) (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    (a a' b : D.X) : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau (a + a') b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (cP D (TW W) a) (lift (cP D (TW W) a') (cP D (TW W) b))).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (ψW.tau a' b)) := by sorry
