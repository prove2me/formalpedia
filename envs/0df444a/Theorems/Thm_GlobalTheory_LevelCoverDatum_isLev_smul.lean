-- Prove2me | Theorems.Thm_GlobalTheory_LevelCoverDatum_isLev_smul
-- name    : GlobalTheory.LevelCoverDatum.isLev_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:59.983464+00:00
-- url     : https://prove2.me/theorems/7a199c88-d5f8-4698-b6a0-2cae323dcda7
-- title:
--   Level Cover Datum: is Lev smul
-- statement:
--   The Level Cover Datum construction uses the is Lev smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/AdmissibleSmulIffOfCoprime.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/AdmissibleSmulIffOfCoprime.lean#L76-L84

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
set_option autoImplicit false
open NumberField
open CategoryTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ}
set_option synthInstance.maxHeartbeats 200000

theorem GlobalTheory.LevelCoverDatum.isLev_smul (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) (a : d.c₂.F) (ha : a ≠ 0) :
    _root_.Formalism.L2.Pj.DeltaDat.IsLev { d with cδ := a • d.cδ } := by sorry
