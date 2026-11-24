-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_add
-- name    : GlobalTheory.CompanionTheory.CongIndex.red_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:23.039916+00:00
-- url     : https://prove2.me/theorems/1d2e319e-392e-444c-a5eb-e03446840983
-- title:
--   Cong Index: red add
-- statement:
--   The Cong Index construction uses the red add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L33-L39

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

theorem GlobalTheory.CompanionTheory.CongIndex.red_add {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x y : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) (hy : valuation k y ≤ valuation k (ϖ ^ c)) :
    red ϖ c (x + y) = red ϖ c x + red ϖ c y := by sorry
