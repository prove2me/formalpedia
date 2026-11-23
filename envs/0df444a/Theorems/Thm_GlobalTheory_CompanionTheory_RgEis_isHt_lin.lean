-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_lin
-- name    : GlobalTheory.CompanionTheory.RgEis.isHt_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:03.237281+00:00
-- url     : https://prove2.me/theorems/0f1f4eb8-7dbf-4ebc-83aa-2a3e35474440
-- title:
--   Rg Eis: is Ht lin
-- statement:
--   The Rg Eis construction uses the is Ht lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L17-L22

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

theorem GlobalTheory.CompanionTheory.RgEis.isHt_lin {Γ K P : Subgroup G} {η θ : G → ℝ} (x y : ℝ) (h₁ : IsHt Γ K P η) (h₂ : IsHt Γ K P θ) :
    IsHt Γ K P fun g => x * η g + y * θ g := by sorry
