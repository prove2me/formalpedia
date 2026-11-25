-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_gramAt_conjTranspose
-- name    : GlobalTheory.CompanionTheory.Ar.PB.gramAt_conjTranspose
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:00:37.323608+00:00
-- url     : https://prove2.me/theorems/73844c00-35d6-5dc5-ac5f-92c163e4ae16
-- title:
--   PB: gram At conj Transpose
-- statement:
--   The PB construction uses the gram At conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L311-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L311-L314

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

theorem GlobalTheory.CompanionTheory.Ar.PB.gramAt_conjTranspose {M : LieModel G ξ Li} {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ Z} {r : ℕ}
    {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ} (h : M.GramAt L z b Γ) : M.GramAt L z b Γᴴ := by sorry
