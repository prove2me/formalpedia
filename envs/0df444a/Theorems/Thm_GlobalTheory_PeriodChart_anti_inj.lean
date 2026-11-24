-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_anti_inj
-- name    : GlobalTheory.PeriodChart.anti_inj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:18.766916+00:00
-- url     : https://prove2.me/theorems/efcdc3e5-ccf4-41e6-b5f4-b40d0dd62715
-- title:
--   Period Chart: anti inj
-- statement:
--   The Period Chart construction uses the anti inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L285-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L285-L288

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}

theorem GlobalTheory.PeriodChart.anti_inj {Z Z' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z, anti Z z = anti Z' z) : Z = Z' := by sorry
