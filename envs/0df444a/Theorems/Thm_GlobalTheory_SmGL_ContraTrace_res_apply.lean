-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_ContraTrace_res_apply
-- name    : GlobalTheory.SmGL.ContraTrace.res_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:40.29615+00:00
-- url     : https://prove2.me/theorems/e61c7504-bdfd-4d71-aea1-97aafbbbfce0
-- title:
--   Contra Trace: res apply
-- statement:
--   The Contra Trace construction uses the res apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContraAdmissibleTrace.lean#L20-L21

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

theorem GlobalTheory.SmGL.ContraTrace.res_apply (π : Representation ℂ G V) (K : Subgroup G) (l : fixed (contra π) K)
    (v : fixed π K) : res π K l v = (l.1 : Module.Dual ℂ V) v.1 := by sorry
