-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_levRep_mk
-- name    : GlobalTheory.LevelPairing.levRep_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:02:40.569796+00:00
-- url     : https://prove2.me/theorems/10df1afc-07c2-4e8e-ad1e-669babfdb745
-- title:
--   Level Pairing: lev Rep mk
-- statement:
--   The Level Pairing construction uses the lev Rep mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L98-L100

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

theorem GlobalTheory.LevelPairing.levRep_mk (x : Dw.La) :
    levRep (Submodule.Quotient.mk x : LevQ Dw l) - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by sorry
