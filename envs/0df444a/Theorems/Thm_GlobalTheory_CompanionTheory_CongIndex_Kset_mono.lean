-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_Kset_mono
-- name    : GlobalTheory.CompanionTheory.CongIndex.Kset_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:21.04761+00:00
-- url     : https://prove2.me/theorems/10161ca0-ad0a-4016-9e7e-3911489fbd17
-- title:
--   Cong Index: Kset mono
-- statement:
--   The Cong Index construction uses the Kset mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L89-L91

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

theorem GlobalTheory.CompanionTheory.CongIndex.Kset_mono {ϖ : k} (h1 : valuation k ϖ < 1) {c c' : Fin N → Fin N → ℕ}
    (h : ∀ i j, c i j ≤ c' i j) : Kset ϖ c' ⊆ Kset ϖ c := by sorry
