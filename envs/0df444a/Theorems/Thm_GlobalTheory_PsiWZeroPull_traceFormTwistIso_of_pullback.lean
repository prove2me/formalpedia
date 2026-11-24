-- Prove2me | Theorems.Thm_GlobalTheory_PsiWZeroPull_traceFormTwistIso_of_pullback
-- name    : GlobalTheory.PsiWZeroPull.traceFormTwistIso_of_pullback
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:19.598608+00:00
-- url     : https://prove2.me/theorems/87b94818-aedb-489b-9dd2-0d417894edb5
-- title:
--   Psi WZero Pull: trace Form Twist Iso of pullback
-- statement:
--   The Psi WZero Pull construction uses the trace Form Twist Iso of pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TraceFormTwistIsoOfPullback.lean#L90-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TraceFormTwistIsoOfPullback.lean#L90-L183

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
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
set_option maxHeartbeats 1000000

theorem GlobalTheory.PsiWZeroPull.traceFormTwistIso_of_pullback (hD : IsPullDeg φ D D') {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (ιD : D.OAct O) (ιD' : D'.OAct O) (hx : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y)
    (hact : ∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))
    (w0 : O) (h : TraceFormTwistIso D ιD w0) : TraceFormTwistIso D' ιD' w0 := by sorry
