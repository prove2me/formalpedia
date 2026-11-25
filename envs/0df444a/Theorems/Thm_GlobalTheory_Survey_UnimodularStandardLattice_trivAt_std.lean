-- Prove2me | Theorems.Thm_GlobalTheory_Survey_UnimodularStandardLattice_trivAt_std
-- name    : GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:28.401652+00:00
-- url     : https://prove2.me/theorems/331a028b-aea0-5260-90de-09b7c21fbf2a
-- title:
--   Unimodular Standard Lattice: triv At std
-- statement:
--   The Unimodular Standard Lattice construction uses the triv At std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/UnimodularStandardLattice.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/UnimodularStandardLattice.lean#L65-L66

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
omit [IsCMField E]

theorem GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std (bad : ℕ) : (⟨stdLat E n⟩ : GenLat E n).TrivAt bad := by sorry
