-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagTie_frames_centre
-- name    : GlobalTheory.CompanionTheory.Ar.PB.FlagTie.frames_centre
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:11.938666+00:00
-- url     : https://prove2.me/theorems/270fb3ef-01ae-5936-9b99-87efcaaed7bb
-- title:
--   Flag Tie: frames centre
-- statement:
--   The Flag Tie construction uses the frames centre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L431-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean#L431-L437

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
variable {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem GlobalTheory.CompanionTheory.Ar.PB.FlagTie.frames_centre (tie : FlagTie M 𝔐) {R : Type} [Field R] {z : Spec (CommRingCat.of R) ⟶ 𝔐.X}
    {w : (Σ k, baseIdx ι M.blk k) → R} (hw : CoordsAt 𝔐.ξ M.x z w)
    {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (h : M.IsFrame F) (h' : M.GoodAt F (mCoordIdeal w))
    (τ : CMType H) : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) ⟨centre z, 𝔐.all _⟩ ∧
      (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) ⟨centre z, 𝔐.all _⟩ := by sorry
