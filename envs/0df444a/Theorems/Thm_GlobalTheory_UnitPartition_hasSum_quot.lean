-- Prove2me | Theorems.Thm_GlobalTheory_UnitPartition_hasSum_quot
-- name    : GlobalTheory.UnitPartition.hasSum_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:45.749431+00:00
-- url     : https://prove2.me/theorems/fc7c8ba3-da9e-4a2f-85a1-d6855ccaaa38
-- title:
--   Unit Partition: has Sum quot
-- statement:
--   The Unit Partition construction uses the has Sum quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L11-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open GlobalTheory.UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem GlobalTheory.UnitPartition.hasSum_quot {G : Type} [Group G] (T : Subgroup G) [Finite T] (f : G ⧸ T → ℝ) (s : ℝ)
    (hf : HasSum f s) : HasSum (fun g : G => f (g : G ⧸ T) / Nat.card T) s := by sorry
