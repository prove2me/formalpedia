-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Herm_fin_orbit
-- name    : GlobalTheory.ThK.Dbl.Herm.fin_orbit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:29.537428+00:00
-- url     : https://prove2.me/theorems/4de82cc3-3b2a-4ff8-95da-59461bf2f7bb
-- title:
--   Herm: fin orbit
-- statement:
--   The Herm construction uses the fin orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FinOrbit.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FinOrbit.lean#L12-L36

import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FinOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Herm
open scoped InnerProductSpace Cardinal
open PositivityTheory.ThKF.Abs Topology
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P : Type} [AddCommGroup P] [Module ℂ P]

theorem GlobalTheory.ThK.Dbl.Herm.fin_orbit [BaireSpace G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hu : Function.Injective u)
    (hc : ∀ x, Continuous (u x)) (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ P ≤ ℵ₀) (x : P) {C : Set G}
    (hC : IsCompact C) : ∃ V : Submodule ℂ P, FiniteDimensional ℂ V ∧ ∀ g ∈ C, ρ g x ∈ V := by sorry
