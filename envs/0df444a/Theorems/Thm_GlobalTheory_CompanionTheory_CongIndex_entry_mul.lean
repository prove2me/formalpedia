-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_entry_mul
-- name    : GlobalTheory.CompanionTheory.CongIndex.entry_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:49.632963+00:00
-- url     : https://prove2.me/theorems/cbdc7a8e-5a0c-4c2e-83d3-524c688bb28e
-- title:
--   Cong Index: entry mul
-- statement:
--   The Cong Index construction uses the entry mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L98-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L98-L118

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

theorem GlobalTheory.CompanionTheory.CongIndex.entry_mul {ϖ : k} (h1 : valuation k ϖ < 1) {c : Fin N → Fin N → ℕ} {i j : Fin N}
    (hij : i ≠ j) (hc : ∀ l, c i j + 1 ≤ c i l + c l j) {g h : GL (Fin N) k}
    (hg : g ∈ Kset ϖ c) (hh : h ∈ Kset ϖ c) :
    ∃ e : k, valuation k e ≤ valuation k (ϖ ^ (c i j + 1)) ∧
      ((g * h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
        (g : Matrix (Fin N) (Fin N) k) i j + (h : Matrix (Fin N) (Fin N) k) i j + e := by sorry
