-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_gnorm_add_le
-- name    : GlobalTheory.HermFrame.gnorm_add_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:11.952901+00:00
-- url     : https://prove2.me/theorems/4498441b-bbaf-4188-9801-c6d82d49e02e
-- title:
--   Herm Frame: gnorm add le
-- statement:
--   The Herm Frame construction uses the gnorm add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L105-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

theorem GlobalTheory.HermFrame.gnorm_add_le {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    gnorm H (v + w) ≤ gnorm H v + gnorm H w := by sorry
