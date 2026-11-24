-- Prove2me | Theorems.Thm_GlobalTheory_Klein_const_mem_intFun
-- name    : GlobalTheory.Klein.const_mem_intFun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:52.648337+00:00
-- url     : https://prove2.me/theorems/08b42bae-394d-4b08-a899-5e98784d7260
-- title:
--   Klein: const mem int Fun
-- statement:
--   The Klein construction uses the const mem int Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L45-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.Klein.const_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {c : ℂ} (hc : c ∈ intAt ι) :
    (fun _ => c) ∈ intFun ι L r := by sorry
