-- Prove2me | Theorems.Thm_GlobalTheory_Survey_UnimodularStandardLattice_unimod_std
-- name    : GlobalTheory.Survey.UnimodularStandardLattice.unimod_std
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:51.956011+00:00
-- url     : https://prove2.me/theorems/a0ef3064-f579-4aed-8106-fa3a0385e5d7
-- title:
--   Unimodular Standard Lattice: unimod std
-- statement:
--   The Unimodular Standard Lattice construction uses the unimod std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/UnimodularStandardLattice.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/UnimodularStandardLattice.lean#L43-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaSpanAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_UnimodularStandardLattice
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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.UnimodularStandardLattice
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
set_option autoImplicit false
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.Survey.UnimodularStandardLattice.unimod_std :
    (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n).Unimod := by sorry
