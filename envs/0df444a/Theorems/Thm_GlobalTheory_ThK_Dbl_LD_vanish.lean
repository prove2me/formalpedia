-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_vanish
-- name    : GlobalTheory.ThK.Dbl.LD.vanish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:15.266788+00:00
-- url     : https://prove2.me/theorems/39573ff6-6f5d-4e9b-ac38-cf8149aebe95
-- title:
--   LD: vanish
-- statement:
--   The LD construction uses the vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L77-L91

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
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
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]

theorem GlobalTheory.ThK.Dbl.LD.vanish (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ}
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, l φ = 0 := by sorry
