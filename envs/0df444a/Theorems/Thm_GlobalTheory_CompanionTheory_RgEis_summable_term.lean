-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_summable_term
-- name    : GlobalTheory.CompanionTheory.RgEis.summable_term
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:10.798405+00:00
-- url     : https://prove2.me/theorems/fc1710eb-ad8b-4cc0-93f2-7d81f646c855
-- title:
--   Rg Eis: summable term
-- statement:
--   The Rg Eis construction uses the summable term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L125-L128

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}

theorem GlobalTheory.CompanionTheory.RgEis.summable_term [CompleteSpace W] {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    Summable fun q : Cos P Γ => Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w := by sorry
