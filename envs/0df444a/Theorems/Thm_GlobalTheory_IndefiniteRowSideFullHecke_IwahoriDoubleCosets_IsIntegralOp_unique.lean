-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IwahoriDoubleCosets_IsIntegralOp_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp.unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:01.980643+00:00
-- url     : https://prove2.me/theorems/ece94577-75f1-46f1-81df-726c5ce9aa08
-- title:
--   Is Integral Op: unique
-- statement:
--   The Is Integral Op construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean#L19-L24

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {A B : V →ₗ[ℂ] V}
    (hA : IsIntegralOp μ π f A) (hB : IsIntegralOp μ π f B) : A = B := by sorry
