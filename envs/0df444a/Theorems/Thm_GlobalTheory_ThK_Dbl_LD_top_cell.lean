-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_top_cell
-- name    : GlobalTheory.ThK.Dbl.LD.top_cell
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:03.455051+00:00
-- url     : https://prove2.me/theorems/c4d0bdc1-2f0e-414b-a923-fc4130a2d286
-- title:
--   LD: top cell
-- statement:
--   The LD construction uses the top cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L37-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L37-L73

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

theorem GlobalTheory.ThK.Dbl.LD.top_cell (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    {g : GL (Fin d) k} (hg : g.1ᵀ = g.1) {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X.det = 0 → φ X = 0) :
    l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by sorry
