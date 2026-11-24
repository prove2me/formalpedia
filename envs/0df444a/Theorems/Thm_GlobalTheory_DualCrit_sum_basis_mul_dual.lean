-- Prove2me | Theorems.Thm_GlobalTheory_DualCrit_sum_basis_mul_dual
-- name    : GlobalTheory.DualCrit.sum_basis_mul_dual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:52:09.327798+00:00
-- url     : https://prove2.me/theorems/592a8aa8-a772-40e9-a328-c370852530b4
-- title:
--   Dual Crit: sum basis mul dual
-- statement:
--   The Dual Crit construction uses the sum basis mul dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfTraceDual.lean#L30-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfTraceDual.lean#L30-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DualCrit

theorem GlobalTheory.DualCrit.sum_basis_mul_dual {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (σ σ' : E →+* K) :
    ∑ j, σ' (b j) * σ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b j) =
      if σ' = σ then 1 else 0 := by sorry
