-- Prove2me | Theorems.Thm_GlobalTheory_SemisimpleCount_injective_of_ne_zero
-- name    : GlobalTheory.SemisimpleCount.injective_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:25.092921+00:00
-- url     : https://prove2.me/theorems/f1cdde6d-15b6-49dd-aa3e-7ff6f871a9ec
-- title:
--   Semisimple Count: injective of ne zero
-- statement:
--   The Semisimple Count construction uses the injective of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L94-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
variable {S : Type} [AddCommGroup S] [Module Rg S]

theorem GlobalTheory.SemisimpleCount.injective_of_ne_zero {A : Type} [AddCommGroup A] [Module Rg A] [IsSimpleModule Rg S]
    {f : S →ₗ[Rg] A} (hf : f ≠ 0) : Function.Injective f := by sorry
