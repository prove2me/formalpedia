-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_of_le
-- name    : GlobalTheory.CompanionTheory.CongIndex.red_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:57.315114+00:00
-- url     : https://prove2.me/theorems/3b212bc3-3271-4fc9-ab45-bdd43d4ad3af
-- title:
--   Cong Index: red of le
-- statement:
--   The Cong Index construction uses the red of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L22-L26

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

theorem GlobalTheory.CompanionTheory.CongIndex.red_of_le {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) :
    red ϖ c x = IsLocalRing.residue _ ⟨x * (ϖ ^ c)⁻¹, scaled_le h0 hx⟩ := by sorry
