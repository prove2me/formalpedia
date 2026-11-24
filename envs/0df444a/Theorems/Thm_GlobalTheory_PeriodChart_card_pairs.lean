-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_card_pairs
-- name    : GlobalTheory.PeriodChart.card_pairs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:33.936352+00:00
-- url     : https://prove2.me/theorems/fd916a7d-57e8-4cdd-ba05-92bfcfe9863f
-- title:
--   Period Chart: card pairs
-- statement:
--   The Period Chart construction uses the card pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L897-L927
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L897-L927

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
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}

theorem GlobalTheory.PeriodChart.card_pairs {p q : ℕ} (hty : IsTypeFn H p q ty) :
    Nat.card {x : Fin g × Fin g // ty x.1 = ComplexEmbedding.conjugate (ty x.2)} = finrank ℚ E * p * q := by sorry
