-- Prove2me | Theorems.Thm_GlobalTheory_BrauerZero_ind_ind_of_le
-- name    : GlobalTheory.BrauerZero.ind_ind_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:03:39.021498+00:00
-- url     : https://prove2.me/theorems/c28ee78a-71fd-4320-8488-c7658dbb5084
-- title:
--   Brauer Zero: ind ind of le
-- statement:
--   The Brauer Zero construction uses the ind ind of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedClassFunctionFromSubgroupTrans.lean#L7-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedClassFunctionFromSubgroupTrans.lean#L7-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
open GlobalTheory GlobalTheory.BrauerZero

theorem GlobalTheory.BrauerZero.ind_ind_of_le {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A)
    (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by sorry
