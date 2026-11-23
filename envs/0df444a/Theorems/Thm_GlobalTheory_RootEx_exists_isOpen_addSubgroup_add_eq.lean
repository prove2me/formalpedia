-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_exists_isOpen_addSubgroup_add_eq
-- name    : GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:39.681515+00:00
-- url     : https://prove2.me/theorems/cd1cb0cf-4142-4be2-81fc-88dd024865d1
-- title:
--   Root Ex: exists is Open add Subgroup add eq
-- statement:
--   The Root Ex construction uses the exists is Open add Subgroup add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria.lean#L12-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria.lean#L12-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.RootEx
open MeasureTheory ValuativeRel Matrix
open scoped Topology Pointwise

theorem GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq {X : Type*}
    [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) (hcs : IsCompact (tsupport Φ)) :
    ∃ Λ : AddSubgroup X, IsOpen (Λ : Set X) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by sorry
