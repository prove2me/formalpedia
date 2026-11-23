-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_sec_mul
-- name    : GlobalTheory.CompanionTheory.RgEisSec.sec_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:45.7811+00:00
-- url     : https://prove2.me/theorems/e91218b4-1115-4148-bf76-69f4ab2ae3a8
-- title:
--   Rg Eis Sec: sec mul
-- statement:
--   The Rg Eis Sec construction uses the sec mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionLawHolds.lean#L19-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionLawHolds.lean#L19-L44

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisSec
variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.CompanionTheory.RgEisSec.sec_mul {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} (hch : IsCh Γ P c)
    {w : W} (hw : w ∈ secSp K P c ρ) {p : G} (hp : p ∈ P) (k : K) :
    sec K P c ρ (p * k) w = c p • ρ k⁻¹ w := by sorry
