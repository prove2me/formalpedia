-- Prove2me | Theorems.Thm_GlobalTheory_QuadTrace_bar_rt
-- name    : GlobalTheory.QuadTrace.bar_rt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:48.110558+00:00
-- url     : https://prove2.me/theorems/af64dbc5-290b-4e15-9f8f-0a19c3950bd0
-- title:
--   Quad Trace: bar rt
-- statement:
--   The Quad Trace construction uses the bar rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CmHostIdempotentTraceEqOne.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CmHostIdempotentTraceEqOne.lean#L9-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CmHostIdempotentTraceEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField
open GlobalTheory GlobalTheory.QuadTrace

theorem GlobalTheory.QuadTrace.bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by sorry
