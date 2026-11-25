-- Prove2me | Theorems.Thm_GlobalTheory_Survey_UnimodularStandardLattice_mem_stdLat
-- name    : GlobalTheory.Survey.UnimodularStandardLattice.mem_stdLat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:33.380927+00:00
-- url     : https://prove2.me/theorems/6dbdb58e-9b65-5a23-9575-7e8a2318fbde
-- title:
--   Unimodular Standard Lattice: mem std Lat
-- statement:
--   The Unimodular Standard Lattice construction uses the mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/UnimodularStandardLattice.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/UnimodularStandardLattice.lean#L15-L16

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

theorem GlobalTheory.Survey.UnimodularStandardLattice.mem_stdLat (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by sorry
