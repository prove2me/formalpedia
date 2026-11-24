-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IwahoriDoubleCosets_HasTrace_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace.unique
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:11.097011+00:00
-- url     : https://prove2.me/theorems/9253df86-fb38-4af5-82c0-97fbce040b04
-- title:
--   Has Trace: unique
-- statement:
--   The Has Trace construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean#L35-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {c d : ℂ}
    (hc : HasTrace μ π f c) (hd : HasTrace μ π f d) : c = d := by sorry
