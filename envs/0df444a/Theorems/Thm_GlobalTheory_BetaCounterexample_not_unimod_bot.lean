-- Prove2me | Theorems.Thm_GlobalTheory_BetaCounterexample_not_unimod_bot
-- name    : GlobalTheory.BetaCounterexample.not_unimod_bot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:24.300263+00:00
-- url     : https://prove2.me/theorems/be37770b-49e1-479d-94a2-3296b551449e
-- title:
--   Beta Counterexample: not unimod bot
-- statement:
--   The Beta Counterexample construction uses the not unimod bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean#L94-L101

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

theorem GlobalTheory.BetaCounterexample.not_unimod_bot {n : ℕ} (hn : 0 < n) : ¬ (⟨⊥⟩ : GenLat E n).Unimod := by sorry
