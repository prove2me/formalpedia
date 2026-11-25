-- Prove2me | Theorems.Thm_GlobalTheory_EpsIso_isHomeomorph_of_isPullback
-- name    : GlobalTheory.EpsIso.isHomeomorph_of_isPullback
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:49.260147+00:00
-- url     : https://prove2.me/theorems/880950cb-21a6-5a2a-9b77-c88012686986
-- title:
--   Eps Iso: is Homeomorph of is Pullback
-- statement:
--   The Eps Iso construction uses the is Homeomorph of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfIdModEpsThickening.lean#L118-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfIdModEpsThickening.lean#L118-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso

theorem GlobalTheory.EpsIso.isHomeomorph_of_isPullback {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K}
    {π : Y' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'}
    (h : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) :
    IsClosedImmersion j ∧ IsHomeomorph j := by sorry
