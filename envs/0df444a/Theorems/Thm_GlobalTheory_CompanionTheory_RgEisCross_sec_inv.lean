-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisCross_sec_inv
-- name    : GlobalTheory.CompanionTheory.RgEisCross.sec_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:23.811604+00:00
-- url     : https://prove2.me/theorems/ca130c69-8357-456c-92e2-7f5e982af7c4
-- title:
--   Rg Eis Cross: sec inv
-- statement:
--   The Rg Eis Cross construction uses the sec inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossingOfWallsAndHeights.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossingOfWallsAndHeights.lean#L12-L21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicSeriesUniformTubeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionInvarianceCosetSumStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSeriesSummableShiftedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossingOfWallsAndHeights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisCross

theorem GlobalTheory.CompanionTheory.RgEisCross.sec_inv {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {w : W} (hP : IsPar Γ K P c)
    (law : ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) :
    ∀ γ ∈ Γ, γ ∈ P → ∀ x, sec K P c ρ (γ * x) w = sec K P c ρ x w := by sorry
