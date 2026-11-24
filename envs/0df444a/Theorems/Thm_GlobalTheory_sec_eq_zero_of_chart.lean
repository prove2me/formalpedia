-- Prove2me | Theorems.Thm_GlobalTheory_sec_eq_zero_of_chart
-- name    : GlobalTheory.sec_eq_zero_of_chart
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:33.854325+00:00
-- url     : https://prove2.me/theorems/15a2eb03-2064-491a-9fcc-7522e1663754
-- title:
--   Global Theory: sec eq zero of chart
-- statement:
--   The Global Theory construction uses the sec eq zero of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroOfDvdPowUniformiser.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroOfDvdPowUniformiser.lean#L11-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroOfDvdPowUniformiser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.sec_eq_zero_of_chart {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by sorry
