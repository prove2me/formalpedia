-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_eq_case
-- name    : GlobalTheory.ThK.Dbl.LD.eq_case
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:03:15.640629+00:00
-- url     : https://prove2.me/theorems/617597dd-bcf8-4079-a7b4-ead8c514e1aa
-- title:
--   LD: eq case
-- statement:
--   The LD construction uses the eq case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L106-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L106-L143

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

theorem GlobalTheory.ThK.Dbl.LD.eq_case (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t)
    (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) (g : GL (Fin d) k) :
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by sorry
