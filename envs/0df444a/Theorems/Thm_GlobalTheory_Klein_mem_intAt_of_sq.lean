-- Prove2me | Theorems.Thm_GlobalTheory_Klein_mem_intAt_of_sq
-- name    : GlobalTheory.Klein.mem_intAt_of_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:19.187979+00:00
-- url     : https://prove2.me/theorems/14acab3a-7c5d-4648-bed5-46bb664bff0a
-- title:
--   Klein: mem int At of sq
-- statement:
--   The Klein construction uses the mem int At of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L37-L40

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

theorem GlobalTheory.Klein.mem_intAt_of_sq (ι : ℂ ≃+* ℂ_[p]) {c : ℂ} (h : c ^ 2 ∈ intAt ι) : c ∈ intAt ι := by sorry
