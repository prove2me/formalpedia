-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_levelFourierDatum_mk
-- name    : GlobalTheory.LevelPairing.levelFourierDatum_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:21.986334+00:00
-- url     : https://prove2.me/theorems/2d1037bf-6e8b-4617-a6a5-1cb08fcbd81f
-- title:
--   Level Pairing: level Fourier Datum mk
-- statement:
--   The Level Pairing construction uses the level Fourier Datum mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L109-L111

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

theorem GlobalTheory.LevelPairing.levelFourierDatum_mk (c : Coeff l) {n : ℕ} (x0 x : Fin n → Dw.La) :
    x0Dat c x0 (fun b => (Submodule.Quotient.mk (x b) : LevQ Dw l)) = zetaM c ^ pairL (l := l) x0 x := by sorry
