-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrincipalCongruence_isOpen_isCompact_principal
-- name    : GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:28.972548+00:00
-- url     : https://prove2.me/theorems/27b2687f-1a56-4450-9aa6-5c2f1b222a12
-- title:
--   Principal Congruence: is Open is Compact principal
-- statement:
--   The Principal Congruence construction uses the is Open is Compact principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenIsCompactPrincipal.lean#L119-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenIsCompactPrincipal.lean#L119-L127

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

theorem GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
    IsOpen {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} ∧
    IsCompact {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} := by sorry
