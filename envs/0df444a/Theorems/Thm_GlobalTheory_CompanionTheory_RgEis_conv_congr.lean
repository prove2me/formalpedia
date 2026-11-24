-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_conv_congr
-- name    : GlobalTheory.CompanionTheory.RgEis.conv_congr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:18.148804+00:00
-- url     : https://prove2.me/theorems/e68853b3-9cdc-42d7-a60a-b3db51a4d8bd
-- title:
--   Rg Eis: conv congr
-- statement:
--   The Rg Eis construction uses the conv congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L27-L28

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

theorem GlobalTheory.CompanionTheory.RgEis.conv_congr {Γ P : Subgroup G} {l l' : G → ℝ} (h : Conv Γ P l) (e : ∀ g, l' g = l g) : Conv Γ P l' := by sorry
