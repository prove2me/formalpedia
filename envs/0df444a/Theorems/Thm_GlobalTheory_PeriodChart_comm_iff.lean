-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_comm_iff
-- name    : GlobalTheory.PeriodChart.comm_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:26.426233+00:00
-- url     : https://prove2.me/theorems/0a5dd0f2-d94d-4af2-9c76-36f6906bac27
-- title:
--   Period Chart: comm iff
-- statement:
--   The Period Chart construction uses the comm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L604-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L604-L622

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
omit [IsCMField E]

theorem GlobalTheory.PeriodChart.comm_iff (ty ty' : Fin g → (E →+* ℂ)) (W : Matrix (Fin g) (Fin g) ℂ) :
    (∀ a, dg ty a * W = W * dg ty' a) ↔ ∀ i j, ¬ ty i = ty' j → W i j = 0 := by sorry
