-- Prove2me | Theorems.Thm_GlobalTheory_firstJet_eq_aug_add_sum
-- name    : GlobalTheory.firstJet_eq_aug_add_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:43.087924+00:00
-- url     : https://prove2.me/theorems/0590a33d-8bef-4123-9fbf-9dce8fbf34a5
-- title:
--   Global Theory: first Jet eq aug add sum
-- statement:
--   The Global Theory construction uses the first Jet eq aug add sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstJetEqProdTangent.lean#L18-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstJetEqProdTangent.lean#L18-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SqZero TrivSqZeroExt

theorem GlobalTheory.firstJet_eq_aug_add_sum {R : Type} [CommRing R] {d : ℕ} (a : JetR R (Fin d) 1) :
    a = algebraMap R _ (jetAug R (Fin d) 1 a) +
      ∑ j, algebraMap R _ (dualLift (Pi.single j (1 : R)) a).snd * zR 1 j := by sorry
