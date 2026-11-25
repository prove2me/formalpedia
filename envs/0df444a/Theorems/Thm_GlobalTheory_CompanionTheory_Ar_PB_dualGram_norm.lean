-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_dualGram_norm
-- name    : GlobalTheory.CompanionTheory.Ar.PB.dualGram_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:11.830954+00:00
-- url     : https://prove2.me/theorems/0116bc77-ff51-4298-ba6f-8e49e94211b0
-- title:
--   PB: dual Gram norm
-- statement:
--   The PB construction uses the dual Gram norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L327-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L327-L329

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over Z} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem GlobalTheory.CompanionTheory.Ar.PB.dualGram_norm {r : ℕ} {Γ Γ' : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.IsHermitian) (h : Γ'ᵀ * Γ = 1)
    {y u : Fin r → ℂ} (hu : ∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) : star y ⬝ᵥ Γ' *ᵥ y = star u ⬝ᵥ Γ *ᵥ u := by sorry
