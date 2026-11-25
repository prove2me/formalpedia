-- Prove2me | Theorems.Thm_GlobalTheory_RowChartCounterexample_vV_nonneg
-- name    : GlobalTheory.RowChartCounterexample.vV_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:49.439807+00:00
-- url     : https://prove2.me/theorems/92c1c4bc-223e-4ef1-96ac-11d1245ae08e
-- title:
--   Row Chart Counterexample: v V nonneg
-- statement:
--   The Row Chart Counterexample construction uses the v V nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean#L23-L31

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

theorem GlobalTheory.RowChartCounterexample.vV_nonneg (T : CDVR) (a : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by sorry
