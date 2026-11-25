-- Prove2me | Theorems.Thm_GlobalTheory_CycInvariants_fixed_iff_mem_Ohat
-- name    : GlobalTheory.CycInvariants.fixed_iff_mem_Ohat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:11.827896+00:00
-- url     : https://prove2.me/theorems/ecb5e05f-66e0-5f59-84b7-eb8169ed8ed0
-- title:
--   Cyc Invariants: fixed iff mem Ohat
-- statement:
--   The Cyc Invariants construction uses the fixed iff mem Ohat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerFixedIffMemCompletedIntegers.lean#L88-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerFixedIffMemCompletedIntegers.lean#L88-L153

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycInvariants
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.CycInvariants.fixed_iff_mem_Ohat : ∀ (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act →
    ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 →
      ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by sorry
