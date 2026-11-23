-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_conv_congr
-- name    : GlobalTheory.CompanionTheory.RgEisGal.conv_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:04.656404+00:00
-- url     : https://prove2.me/theorems/72d60f75-a7c4-4f13-84bd-7caafae4a00f
-- title:
--   Rg Eis Gal: conv congr
-- statement:
--   The Rg Eis Gal construction uses the conv congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L121-L124

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

theorem GlobalTheory.CompanionTheory.RgEisGal.conv_congr {Γ P : Subgroup G} {f f' : G → ℝ} (h : Conv Γ P f') (e : ∀ g, f g = f' g) :
    Conv Γ P f := by sorry
