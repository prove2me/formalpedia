-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongruenceBasis_exists_pow_succ_lt
-- name    : GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:17.162809+00:00
-- url     : https://prove2.me/theorems/a10aed7e-f514-4776-bd03-08b295188b58
-- title:
--   Congruence Basis: exists pow succ lt
-- statement:
--   The Congruence Basis construction uses the exists pow succ lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCongruenceSubset.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCongruenceSubset.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCongruenceSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Filter Topology Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongruenceBasis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt {a γ : ValueGroupWithZero k} (ha0 : a ≠ 0) (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ (m + 1) < γ := by sorry
