-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_ContraTrace_smoothOp_contra
-- name    : GlobalTheory.SmGL.ContraTrace.smoothOp_contra
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:38:56.61452+00:00
-- url     : https://prove2.me/theorems/e6366652-2898-4c83-999a-9801b80d3cdf
-- title:
--   Contra Trace: smooth Op contra
-- statement:
--   The Contra Trace construction uses the smooth Op contra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L50-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.ContraTrace
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.SmGL.ContraTrace.smoothOp_contra [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by sorry
