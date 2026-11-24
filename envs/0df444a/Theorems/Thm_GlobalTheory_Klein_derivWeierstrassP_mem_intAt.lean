-- Prove2me | Theorems.Thm_GlobalTheory_Klein_derivWeierstrassP_mem_intAt
-- name    : GlobalTheory.Klein.derivWeierstrassP_mem_intAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:45.123639+00:00
-- url     : https://prove2.me/theorems/1586a854-7c00-4954-82fb-b5657d434f16
-- title:
--   Klein: deriv Weierstrass P mem int At
-- statement:
--   The Klein construction uses the deriv Weierstrass P mem int At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L56-L67

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

theorem GlobalTheory.Klein.derivWeierstrassP_mem_intAt {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (hg : Good ι L r)
    (hz : Red ι L r z) : L.derivWeierstrassP z ∈ intAt ι := by sorry
