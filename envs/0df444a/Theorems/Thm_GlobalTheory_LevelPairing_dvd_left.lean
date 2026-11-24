-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_dvd_left
-- name    : GlobalTheory.LevelPairing.dvd_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:20.242866+00:00
-- url     : https://prove2.me/theorems/1b8e7b81-91ac-478e-a0e5-0248cb1a226e
-- title:
--   Level Pairing: dvd left
-- statement:
--   The Level Pairing construction uses the dvd left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L53-L57

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem GlobalTheory.LevelPairing.dvd_left {x : Dw.La} (y : Dw.La) (hx : x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • y) := by sorry
