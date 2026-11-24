-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LatticePoint_isOpen_valBall
-- name    : GlobalTheory.CompanionTheory.LatticePoint.isOpen_valBall
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:55.146017+00:00
-- url     : https://prove2.me/theorems/5f6317c0-6f7e-46ed-b13f-3cfd1efe6466
-- title:
--   Lattice Point: is Open val Ball
-- statement:
--   The Lattice Point construction uses the is Open val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCompactOpenSubgroupMem.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCompactOpenSubgroupMem.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCompactOpenSubgroupMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticePoint

theorem GlobalTheory.CompanionTheory.LatticePoint.isOpen_valBall {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by sorry
