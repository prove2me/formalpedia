-- Prove2me | Theorems.Thm_GlobalTheory_LevelCoverDatum_half_unique
-- name    : GlobalTheory.LevelCoverDatum.half_unique
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:06.028695+00:00
-- url     : https://prove2.me/theorems/46a90bac-5250-5821-83b5-5300a4177ade
-- title:
--   Level Cover Datum: half unique
-- statement:
--   The Level Cover Datum construction uses the half unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/AdmissibleSmulIffOfCoprime.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/AdmissibleSmulIffOfCoprime.lean#L58-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_AdmissibleSmulIffOfCoprime
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
open GlobalTheory GlobalTheory.LevelCoverDatum
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj GlobalTheory.LevelPairing
open CategoryTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem GlobalTheory.LevelCoverDatum.half_unique (d d' : DeltaDat Xo c n) (h : d.IsLev) (h' : d'.IsLev) (e : d.l₂ = d'.l₂) :
    d.I = d'.I ∧ d.pd = d'.pd := by sorry
