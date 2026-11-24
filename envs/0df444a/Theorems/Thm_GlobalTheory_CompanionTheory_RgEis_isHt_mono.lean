-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_mono
-- name    : GlobalTheory.CompanionTheory.RgEis.isHt_mono
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:31.210441+00:00
-- url     : https://prove2.me/theorems/a3572a5a-a125-4209-8a0e-568a0cc8b821
-- title:
--   Rg Eis: is Ht mono
-- statement:
--   The Rg Eis construction uses the is Ht mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L14-L15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G]

theorem GlobalTheory.CompanionTheory.RgEis.isHt_mono {Γ K P P' : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) (hP : P' ≤ P) : IsHt Γ K P' η := by sorry
