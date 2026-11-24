-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_sigma_hE_self
-- name    : GlobalTheory.CompanionTheory.SW.BB.RatCoord.sigma_hE_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:03:04.377584+00:00
-- url     : https://prove2.me/theorems/0ef34846-13e6-404b-91ca-f881ff28dea5
-- title:
--   Rat Coord: sigma h E self
-- statement:
--   The Rat Coord construction uses the sigma h E self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceForm.lean#L90-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceForm.lean#L90-L100

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.BB.RatCoord.sigma_hE_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (y : Fin M → E) :
    σ (hE σ J y y) = hE σ J y y := by sorry
