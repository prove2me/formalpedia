-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_val_zpow_iff
-- name    : GlobalTheory.CompanionTheory.CongIndex.val_zpow_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:15.423076+00:00
-- url     : https://prove2.me/theorems/7d4bc3c8-aa39-4228-88c6-77c0ba0e286b
-- title:
--   Cong Index: val zpow iff
-- statement:
--   The Cong Index construction uses the val zpow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L273-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L273-L303

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}

theorem GlobalTheory.CompanionTheory.CongIndex.val_zpow_iff {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1) (m : ℕ) (e : ℤ) (x : k) :
    (valuation k x ≤ valuation k (ϖ ^ m) ∧ valuation k (ϖ ^ e * x) ≤ valuation k (ϖ ^ m)) ↔
      valuation k x ≤ valuation k (ϖ ^ (m + (-e).toNat)) := by sorry
