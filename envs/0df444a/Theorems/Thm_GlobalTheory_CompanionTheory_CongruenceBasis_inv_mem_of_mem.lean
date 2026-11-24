-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongruenceBasis_inv_mem_of_mem
-- name    : GlobalTheory.CompanionTheory.CongruenceBasis.inv_mem_of_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:51.269441+00:00
-- url     : https://prove2.me/theorems/f138bdb5-8f48-403a-ae9b-b45e4278aa31
-- title:
--   Congruence Basis: inv mem of mem
-- statement:
--   The Congruence Basis construction uses the inv mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCongruenceSubset.lean#L21-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCongruenceSubset.lean#L21-L65

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

theorem GlobalTheory.CompanionTheory.CongruenceBasis.inv_mem_of_mem {N : ℕ} {t : ValueGroupWithZero k} (ht : t < 1) (g : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t) (i j : Fin N) :
    valuation k (((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t := by sorry
