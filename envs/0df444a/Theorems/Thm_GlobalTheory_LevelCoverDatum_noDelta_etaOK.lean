-- Prove2me | Theorems.Thm_GlobalTheory_LevelCoverDatum_noDelta_etaOK
-- name    : GlobalTheory.LevelCoverDatum.noDelta_etaOK
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:41.225559+00:00
-- url     : https://prove2.me/theorems/60c95d51-f902-502b-8eaf-23500cb2aeeb
-- title:
--   Level Cover Datum: no Delta eta OK
-- statement:
--   The Level Cover Datum construction uses the no Delta eta OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/AdmissibleSmulIffOfCoprime.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/AdmissibleSmulIffOfCoprime.lean#L131-L139

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

theorem GlobalTheory.LevelCoverDatum.noDelta_etaOK (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).EtaOK ↔ (∀ a, (Xo.univ.eta a).left ≫ m.φ = (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA a).left ≫ m.φ = (Xo.univ.etaA a).left := by sorry
