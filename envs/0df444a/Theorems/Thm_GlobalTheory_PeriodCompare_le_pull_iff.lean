-- Prove2me | Theorems.Thm_GlobalTheory_PeriodCompare_le_pull_iff
-- name    : GlobalTheory.PeriodCompare.le_pull_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:27.513727+00:00
-- url     : https://prove2.me/theorems/d073143d-6fbb-4e40-9a4d-e7a143ab444d
-- title:
--   Period Compare: le pull iff
-- statement:
--   The Period Compare construction uses the le pull iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L297-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L297-L299

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}

theorem GlobalTheory.PeriodCompare.le_pull_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : (L.pull f).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) := by sorry
