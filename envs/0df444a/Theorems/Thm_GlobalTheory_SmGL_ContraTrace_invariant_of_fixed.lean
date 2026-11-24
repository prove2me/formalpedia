-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_ContraTrace_invariant_of_fixed
-- name    : GlobalTheory.SmGL.ContraTrace.invariant_of_fixed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:37:07.442797+00:00
-- url     : https://prove2.me/theorems/602be210-dbf8-40a6-aa06-33e34a192213
-- title:
--   Contra Trace: invariant of fixed
-- statement:
--   The Contra Trace construction uses the invariant of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L23-L27

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

theorem GlobalTheory.SmGL.ContraTrace.invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by sorry
