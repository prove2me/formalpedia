-- Prove2me | Theorems.Thm_GlobalTheory_RowChartCounterexample_embOK_eOf
-- name    : GlobalTheory.RowChartCounterexample.embOK_eOf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:35.105496+00:00
-- url     : https://prove2.me/theorems/f6f4b394-7bf0-4848-9679-93cd0bc2c607
-- title:
--   Row Chart Counterexample: emb OK e Of
-- statement:
--   The Row Chart Counterexample construction uses the emb OK e Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean#L33-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_ImaginaryRootConj
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
open GlobalTheory GlobalTheory.RowChartCounterexample
open Formalism.L2.FormalSeriesBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {C : Type} [Field C]

theorem GlobalTheory.RowChartCounterexample.embOK_eOf {T : CDVR} {V : VF C} {ι : T.Fr →+* C} (h : EmbOK T V ι) :
    0 < eOf T V ∧ ((eOf T V : ℕ) : ℤ) = vV T.V ((V.l : ℕ) : T.Fr) := by sorry
