-- Prove2me | Theorems.Thm_GlobalTheory_Klein_norm_iteratedDeriv_weierstrassP_le_one
-- name    : GlobalTheory.Klein.norm_iteratedDeriv_weierstrassP_le_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:17:37.94355+00:00
-- url     : https://prove2.me/theorems/2fcd28e4-7b91-51b7-bdc2-c4e64ba279c8
-- title:
--   Klein: norm iterated Deriv weierstrass P le one
-- statement:
--   The Klein construction uses the norm iterated Deriv weierstrass P le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L125-L129

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

theorem GlobalTheory.Klein.norm_iteratedDeriv_weierstrassP_le_one : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → ∀ z, Red ι L r z → ∀ k : ℕ, ‖ι (iteratedDeriv (k + 1) L.weierstrassP z)‖ ≤ 1 := by sorry
