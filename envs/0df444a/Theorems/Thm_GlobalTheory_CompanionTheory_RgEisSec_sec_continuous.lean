-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_sec_continuous
-- name    : GlobalTheory.CompanionTheory.RgEisSec.sec_continuous
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:10.359827+00:00
-- url     : https://prove2.me/theorems/52bc8e68-e653-48cf-a795-da4a89b9d9c5
-- title:
--   Rg Eis Sec: sec continuous
-- statement:
--   The Rg Eis Sec construction uses the sec continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionLawHolds.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionLawHolds.lean#L46-L58

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

theorem GlobalTheory.CompanionTheory.RgEisSec.sec_continuous [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by sorry
