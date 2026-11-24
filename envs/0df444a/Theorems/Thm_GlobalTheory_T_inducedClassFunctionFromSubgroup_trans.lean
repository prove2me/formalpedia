-- Prove2me | Theorems.Thm_GlobalTheory_T_inducedClassFunctionFromSubgroup_trans
-- name    : GlobalTheory.T.inducedClassFunctionFromSubgroup_trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:13.710804+00:00
-- url     : https://prove2.me/theorems/893fcc0e-43fa-4363-89f3-efe6ea204907
-- title:
--   T: induced Class Function From Subgroup trans
-- statement:
--   The T construction uses the induced Class Function From Subgroup trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedClassFunctionFromSubgroupTransStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedClassFunctionFromSubgroupTransStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTrans
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.inducedClassFunctionFromSubgroup_trans : ∀ {G : Type} [Group G] [Finite G] (K A : Subgroup G), K ≤ A → ∀ (ψ : K → ℂ), ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by sorry
