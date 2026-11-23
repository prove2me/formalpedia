-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_val_add_le
-- name    : GlobalTheory.CompanionTheory.CongIndex.val_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:29.193852+00:00
-- url     : https://prove2.me/theorems/dfaa9a40-f764-4dd8-855d-dc2cc4025c65
-- title:
--   Cong Index: val add le
-- statement:
--   The Cong Index construction uses the val add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L28-L31

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

theorem GlobalTheory.CompanionTheory.CongIndex.val_add_le {c : ℕ} {ϖ x y : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) (hy : valuation k y ≤ valuation k (ϖ ^ c)) :
    valuation k (x + y) ≤ valuation k (ϖ ^ c) := by sorry
