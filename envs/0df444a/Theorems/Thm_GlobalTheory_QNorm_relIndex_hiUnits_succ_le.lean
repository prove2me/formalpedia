-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_relIndex_hiUnits_succ_le
-- name    : GlobalTheory.QNorm.relIndex_hiUnits_succ_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:01:49.208127+00:00
-- url     : https://prove2.me/theorems/14f84d13-ba89-4154-93c7-aa9298aec18d
-- title:
--   QNorm: rel Index hi Units succ le
-- statement:
--   The QNorm construction uses the rel Index hi Units succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexHigherUnitsSuccLeCard.lean#L18-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexHigherUnitsSuccLeCard.lean#L18-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.relIndex_hiUnits_succ_le :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ),
      w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) →
      (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧
        (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by sorry
