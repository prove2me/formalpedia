-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_pow_le_of_le
-- name    : GlobalTheory.CompanionTheory.CongIndex.pow_le_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:00.856992+00:00
-- url     : https://prove2.me/theorems/04a64be6-913e-488b-948a-e82c40bf1662
-- title:
--   Cong Index: pow le of le
-- statement:
--   The Cong Index construction uses the pow le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L84-L87

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

theorem GlobalTheory.CompanionTheory.CongIndex.pow_le_of_le {ϖ : k} (h1 : valuation k ϖ < 1) {a b : ℕ} (h : a ≤ b) :
    valuation k (ϖ ^ b) ≤ valuation k (ϖ ^ a) := by sorry
