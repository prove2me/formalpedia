-- Prove2me | Theorems.Thm_GlobalTheory_T_isAdmissible_contra_and_smoothTrace_inv
-- name    : GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:35.907304+00:00
-- url     : https://prove2.me/theorems/bbf47ced-3a79-4ada-ad26-6344566819c9
-- title:
--   T: is Admissible contra and smooth Trace inv
-- statement:
--   The T construction uses the is Admissible contra and smooth Trace inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTraceStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTraceStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTraceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by sorry
