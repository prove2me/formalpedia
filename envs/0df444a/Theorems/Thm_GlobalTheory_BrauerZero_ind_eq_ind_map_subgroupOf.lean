-- Prove2me | Theorems.Thm_GlobalTheory_BrauerZero_ind_eq_ind_map_subgroupOf
-- name    : GlobalTheory.BrauerZero.ind_eq_ind_map_subgroupOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:03:52.076377+00:00
-- url     : https://prove2.me/theorems/158d8541-c467-4fac-8022-706315ab8689
-- title:
--   Brauer Zero: ind eq ind map subgroup Of
-- statement:
--   The Brauer Zero construction uses the ind eq ind map subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedClassFunctionMemInducedDegreeOneCharDiff.lean#L9-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedClassFunctionMemInducedDegreeOneCharDiff.lean#L9-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
noncomputable section
open GlobalTheory GlobalTheory.BrauerZero

theorem GlobalTheory.BrauerZero.ind_eq_ind_map_subgroupOf {G : Type} [Group G] [Finite G] (E : Subgroup G) (H : Subgroup E)
    (φ : H → ℂ) :
    ind H φ = ind ((H.map E.subtype).subgroupOf E)
      (fun k => φ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
        ⟨((k : E) : G), k.2⟩)) := by sorry
