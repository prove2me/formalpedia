-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrincipalCongruence_isOpen_congSet
-- name    : GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_congSet
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:55.804138+00:00
-- url     : https://prove2.me/theorems/aa83df0b-c96e-4e70-b3cd-55e149876d46
-- title:
--   Principal Congruence: is Open cong Set
-- statement:
--   The Principal Congruence construction uses the is Open cong Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenIsCompactPrincipal.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenIsCompactPrincipal.lean#L57-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congSet n t) := by sorry
