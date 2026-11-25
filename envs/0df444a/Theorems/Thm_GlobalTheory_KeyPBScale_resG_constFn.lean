-- Prove2me | Theorems.Thm_GlobalTheory_KeyPBScale_resG_constFn
-- name    : GlobalTheory.KeyPBScale.resG_constFn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:15.755648+00:00
-- url     : https://prove2.me/theorems/08c6da63-8adc-4a4f-93c9-68db83e52fa5
-- title:
--   Key PBScale: res G const Fn
-- statement:
--   The Key PBScale construction uses the res G const Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LieBaseChange.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LieBaseChange.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DualNumberRingHomExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LieBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyPBScale

theorem GlobalTheory.KeyPBScale.resG_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a := by sorry
