-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_sesq_of
-- name    : GlobalTheory.OfPeriod.sesq_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:42.33519+00:00
-- url     : https://prove2.me/theorems/daf76498-0bff-44e7-b490-4be4e7535949
-- title:
--   Of Period: sesq of
-- statement:
--   The Of Period construction uses the sesq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L28-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex

theorem GlobalTheory.OfPeriod.sesq_of {n : ℕ} (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ) (z w : Fin n → ℂ) :
    hermForm (Matrix.of fun i j => S (Pi.single i 1) (Pi.single j 1)) z w = S z w := by sorry
