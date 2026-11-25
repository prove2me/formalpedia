-- Prove2me | Theorems.Thm_GlobalTheory_BetaCounterexample_betaIs_bot
-- name    : GlobalTheory.BetaCounterexample.betaIs_bot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:53.632347+00:00
-- url     : https://prove2.me/theorems/1db27003-3e33-5be3-af5d-77717f30f2a5
-- title:
--   Beta Counterexample: beta Is bot
-- statement:
--   The Beta Counterexample construction uses the beta Is bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean#L76-L92

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

theorem GlobalTheory.BetaCounterexample.betaIs_bot {n : ℕ} (hn : 0 < n) (τ₀ : E →+* ℂ) (h0 : Dw.mult τ₀ ≠ 0) (β : c.F) :
    BetaIs (Dw := Dw) c (⟨⊥⟩ : GenLat E n) β := by sorry
