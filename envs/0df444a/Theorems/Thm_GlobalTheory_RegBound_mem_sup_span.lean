-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_mem_sup_span
-- name    : GlobalTheory.RegBound.mem_sup_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:19.908895+00:00
-- url     : https://prove2.me/theorems/f1fe5149-2d16-40fa-815a-4e2027d8c507
-- title:
--   Reg Bound: mem sup span
-- statement:
--   The Reg Bound construction uses the mem sup span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L42-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]

theorem GlobalTheory.RegBound.mem_sup_span {I : Ideal (MvPolynomial σ K)} {h F : MvPolynomial σ K} :
    F ∈ I ⊔ Ideal.span {h} ↔ ∃ A ∈ I, ∃ B, F = A + h * B := by sorry
