-- Prove2me | Theorems.Thm_GlobalTheory_PrimTransc_exists_mul_mem_adjoin
-- name    : GlobalTheory.PrimTransc.exists_mul_mem_adjoin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:10.677573+00:00
-- url     : https://prove2.me/theorems/7f8cbcc2-7345-4a79-b6d4-5ebea377f763
-- title:
--   Prim Transc: exists mul mem adjoin
-- statement:
--   The Prim Transc construction uses the exists mul mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveMonicSeparableSpecialization.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveMonicSeparableSpecialization.lean#L43-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open GlobalTheory GlobalTheory.PrimTransc

theorem GlobalTheory.PrimTransc.exists_mul_mem_adjoin {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F {θ}) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R K d * z ∈ Algebra.adjoin R {θ} := by sorry
