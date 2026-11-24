-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_step_closed
-- name    : GlobalTheory.ThK.Dbl.LD.step_closed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:03:53.849836+00:00
-- url     : https://prove2.me/theorems/e8a1eb20-f8fb-4022-b63f-2603d67959fe
-- title:
--   LD: step closed
-- statement:
--   The LD construction uses the step closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L94-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L94-L129

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

theorem GlobalTheory.ThK.Dbl.LD.step_closed {n d : ℕ} (ih : Claim c n d) {l : (Matrix (Fin (n + 1)) (Fin d) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) (hz : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0) :
    ∀ φ ∈ SB _, l φ = 0 := by sorry
