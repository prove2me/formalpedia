-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_anti_comm_iff
-- name    : GlobalTheory.PeriodChart.anti_comm_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:14.838602+00:00
-- url     : https://prove2.me/theorems/300f578f-c9d8-44f3-973a-f4040111617d
-- title:
--   Period Chart: anti comm iff
-- statement:
--   The Period Chart construction uses the anti comm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L632-L663
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L632-L663

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
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.PeriodChart.anti_comm_iff (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (Z : Matrix (Fin g) (Fin g) ℂ) :
    (∀ z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ↔
      dg ty a * Z = Z * dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by sorry
