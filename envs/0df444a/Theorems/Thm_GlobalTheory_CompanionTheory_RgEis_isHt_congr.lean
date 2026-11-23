-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_congr
-- name    : GlobalTheory.CompanionTheory.RgEis.isHt_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:34.990834+00:00
-- url     : https://prove2.me/theorems/4ccdc6d5-dab6-46e3-b00a-1bb78c52b077
-- title:
--   Rg Eis: is Ht congr
-- statement:
--   The Rg Eis construction uses the is Ht congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L24-L25

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

theorem GlobalTheory.CompanionTheory.RgEis.isHt_congr {Γ K P : Subgroup G} {η θ : G → ℝ} (h : IsHt Γ K P η) (e : ∀ g, θ g = η g) : IsHt Γ K P θ := by sorry
