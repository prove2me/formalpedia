-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_iwahoriProj_surjective
-- name    : GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:53.889354+00:00
-- url     : https://prove2.me/theorems/924d01a1-1b6f-4322-a8d1-667ef866d3f7
-- title:
--   Iwahori Onto: iwahori Proj surjective
-- statement:
--   The Iwahori Onto construction uses the iwahori Proj surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L244-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L244-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto

theorem GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] (V : Type)
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (hπ : IsAdmissible π) :
    Function.Surjective (iwahoriProj π) := by sorry
