-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_sb_matrix_exists_isOpen_addSubgroup
-- name    : GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:17.194127+00:00
-- url     : https://prove2.me/theorems/6219d232-ab1b-487c-a775-d67f6b4a12d4
-- title:
--   Root Ex: sb matrix exists is Open add Subgroup
-- statement:
--   The Root Ex construction uses the sb matrix exists is Open add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria.lean#L76-L83

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

theorem GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix a b k),
      ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧
        ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by sorry
