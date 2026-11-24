-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_entry_le
-- name    : GlobalTheory.CompanionTheory.CongIndex.entry_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:42.93957+00:00
-- url     : https://prove2.me/theorems/76b1c0a4-8a57-410b-b327-1f4742f26b03
-- title:
--   Cong Index: entry le
-- statement:
--   The Cong Index construction uses the entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L93-L96

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

theorem GlobalTheory.CompanionTheory.CongIndex.entry_le {ϖ : k} {c : Fin N → Fin N → ℕ} {g : GL (Fin N) k} (hg : g ∈ Kset ϖ c)
    {i j : Fin N} (hij : i ≠ j) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ c i j) := by sorry
