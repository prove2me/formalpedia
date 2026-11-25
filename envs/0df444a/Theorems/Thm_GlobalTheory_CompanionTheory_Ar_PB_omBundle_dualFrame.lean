-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_omBundle_dualFrame
-- name    : GlobalTheory.CompanionTheory.Ar.PB.omBundle_dualFrame
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:21.235424+00:00
-- url     : https://prove2.me/theorems/0e9de471-31ba-46ec-bc3d-c7bf26fb7d68
-- title:
--   PB: om Bundle dual Frame
-- statement:
--   The PB construction uses the om Bundle dual Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L358-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L358-L398

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}

theorem GlobalTheory.CompanionTheory.Ar.PB.omBundle_dualFrame {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S x) (τ : CMType H) (q : Cpt 𝔐.ξ) {φ : Fin D.q → Module.Dual Ω (𝔐.Vgen (.inr τ))}
    (hφ : (omBundle 𝔐 τ).IsFrameAt φ q) :
    (∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, φ a (v b) = if a = b then 1 else 0) ∧
    ∀ v : Fin D.q → 𝔐.Vgen (.inr τ), (∀ a b, φ a (v b) = if a = b then 1 else 0) →
      (𝔐.V (.inr τ)).IsFrameAt (fun b => (v b : 𝔐.Li)) q := by sorry
