-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_bar_mem_Mb
-- name    : GlobalTheory.LevelPairing.bar_mem_Mb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:29.080289+00:00
-- url     : https://prove2.me/theorems/00c2eff3-7cec-43cc-a37e-bd571ec137eb
-- title:
--   Level Pairing: bar mem Mb
-- statement:
--   The Level Pairing construction uses the bar mem Mb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L42-L45

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

theorem GlobalTheory.LevelPairing.bar_mem_Mb {a : 𝓞 E} (ha : a ∈ Mfr l) : H.bar a ∈ l.Mb := by sorry
