-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_step_row
-- name    : GlobalTheory.ThK.Dbl.LD.step_row
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:03:43.487805+00:00
-- url     : https://prove2.me/theorems/8d2be766-e89c-4904-a5b3-749c3286c6f4
-- title:
--   LD: step row
-- statement:
--   The LD construction uses the step row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L81-L92

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}

theorem GlobalTheory.ThK.Dbl.LD.step_row (hc : ∀ a ≠ 0, c a ≠ 0) {n d : ℕ} {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hz : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0 := by sorry
