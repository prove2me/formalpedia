-- Prove2me | Theorems.Thm_GlobalTheory_traceFormTwistIso_of_overPullback
-- name    : GlobalTheory.traceFormTwistIso_of_overPullback
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:00.027312+00:00
-- url     : https://prove2.me/theorems/5c2d3ba7-76bb-4237-8468-ecba01155e9a
-- title:
--   Global Theory: trace Form Twist Iso of over Pullback
-- statement:
--   The Global Theory construction uses the trace Form Twist Iso of over Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TraceFormTwistIsoOfPullback.lean#L189-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TraceFormTwistIsoOfPullback.lean#L189-L194

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

theorem GlobalTheory.traceFormTwistIso_of_overPullback : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X]
    [Module O D'.X] (ιD : D.OAct O) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) →
    (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) →
    ∀ w0 : O, Geo.Tor.TraceFormTwistIso D ιD w0 → Geo.Tor.TraceFormTwistIso D' ιD' w0 := by sorry
