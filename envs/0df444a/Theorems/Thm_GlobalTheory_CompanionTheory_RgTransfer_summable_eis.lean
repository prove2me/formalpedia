-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_summable_eis
-- name    : GlobalTheory.CompanionTheory.RgTransfer.summable_eis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:46.373742+00:00
-- url     : https://prove2.me/theorems/15deb3f2-9305-4836-8995-fe115d56fa01
-- title:
--   Rg Transfer: summable eis
-- statement:
--   The Rg Transfer construction uses the summable eis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L404-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L404-L410

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}

theorem GlobalTheory.CompanionTheory.RgTransfer.summable_eis {ρ : K →* (W →L[ℂ] W)} [CompleteSpace W] {M : ℝ}
    (hM : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {Λ : G → ℂ} {l : G → ℝ}
    (hl : ∀ g, (Λ g).re = l g) (hc : Conv Γ P l) (g : G) (w : W) :
    Summable fun y : Cos P Γ => Complex.exp (Λ (rep y * g)) • sec K P c ρ (rep y * g) w := by sorry
