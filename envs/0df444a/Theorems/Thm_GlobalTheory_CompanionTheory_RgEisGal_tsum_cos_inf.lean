-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_tsum_cos_inf
-- name    : GlobalTheory.CompanionTheory.RgEisGal.tsum_cos_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:01.432872+00:00
-- url     : https://prove2.me/theorems/b3e056fe-352b-46c1-9cbe-886f8ef63ef5
-- title:
--   Rg Eis Gal: tsum cos inf
-- statement:
--   The Rg Eis Gal construction uses the tsum cos inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L209-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L209-L217

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.RgEisGal.tsum_cos_inf {X : Type} [AddCommMonoid X] [TopologicalSpace X] (Γ S : Subgroup G)
    (f : G → X) : ∑' r : Cos (Γ ⊓ S) Γ, f (rep r) = ∑' q : Cos S Γ, f (rep q) := by sorry
