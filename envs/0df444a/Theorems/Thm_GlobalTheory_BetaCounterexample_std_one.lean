-- Prove2me | Theorems.Thm_GlobalTheory_BetaCounterexample_std_one
-- name    : GlobalTheory.BetaCounterexample.std_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:12.632701+00:00
-- url     : https://prove2.me/theorems/bf7f9694-5cc3-4aae-b53b-c27b41684705
-- title:
--   Beta Counterexample: std one
-- statement:
--   The Beta Counterexample construction uses the std one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean#L15-L26

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
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
open GlobalTheory GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)

theorem GlobalTheory.BetaCounterexample.std_one (n : ℕ) (β : c.F) (hβ : β = 1 ∨ β = -1) :
    β ≠ 0 ∧ BetaIs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β ∧ BetaAbs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β := by sorry
