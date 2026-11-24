-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_surj
-- name    : GlobalTheory.CompanionTheory.CongIndex.red_surj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:55.30395+00:00
-- url     : https://prove2.me/theorems/2020e341-e0ab-4c00-b1e2-c59f9296d3a0
-- title:
--   Cong Index: red surj
-- statement:
--   The Cong Index construction uses the red surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L64-L76

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

theorem GlobalTheory.CompanionTheory.CongIndex.red_surj {ϖ : k} (h0 : ϖ ≠ 0) (c : ℕ)
    (r : IsLocalRing.ResidueField (valuation k).integer) :
    ∃ x : k, valuation k x ≤ valuation k (ϖ ^ c) ∧ red ϖ c x = r := by sorry
