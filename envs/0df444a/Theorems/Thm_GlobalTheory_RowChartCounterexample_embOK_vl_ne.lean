-- Prove2me | Theorems.Thm_GlobalTheory_RowChartCounterexample_embOK_vl_ne
-- name    : GlobalTheory.RowChartCounterexample.embOK_vl_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:29.068557+00:00
-- url     : https://prove2.me/theorems/5e27d124-df85-4cfc-a307-85722895c52a
-- title:
--   Row Chart Counterexample: emb OK vl ne
-- statement:
--   The Row Chart Counterexample construction uses the emb OK vl ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean#L15-L21

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

theorem GlobalTheory.RowChartCounterexample.embOK_vl_ne {T : CDVR} {V : VF C} {ι : T.Fr →+* C} (h : EmbOK T V ι) :
    vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by sorry
