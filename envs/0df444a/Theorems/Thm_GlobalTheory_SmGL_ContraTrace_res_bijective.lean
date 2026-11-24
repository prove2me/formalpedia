-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_ContraTrace_res_bijective
-- name    : GlobalTheory.SmGL.ContraTrace.res_bijective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:14.021063+00:00
-- url     : https://prove2.me/theorems/4ea204df-7649-4218-a2a1-56208c00bdb4
-- title:
--   Contra Trace: res bijective
-- statement:
--   The Contra Trace construction uses the res bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L29-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L29-L42

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

theorem GlobalTheory.SmGL.ContraTrace.res_bijective [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by sorry
