-- Prove2me | Theorems.Thm_GlobalTheory_SW_Decay_exists_fourier
-- name    : GlobalTheory.SW.Decay.exists_fourier
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:48.477584+00:00
-- url     : https://prove2.me/theorems/a1d1e5cf-aac1-4f5c-ab91-7236f3653cd3
-- title:
--   Decay: exists fourier
-- statement:
--   The Decay construction uses the exists fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCusps.lean#L231-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCusps.lean#L231-L361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Decay
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}

theorem GlobalTheory.SW.Decay.exists_fourier (hΨ : IsType Ψ) (N R : ℕ) (hR : 0 < R) :
    ∃ (m c : ℕ) (T : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E) (X : (Fin m → ℝ) → CM Ψ N N),
      0 < c ∧ Function.Injective T ∧ (∀ ν, ccT (T ν) = T ν ∧ Den c (T ν)) ∧ Continuous X ∧
      (∀ x τ, (X x τ).IsHermitian) ∧ ∀ f : CM Ψ N N → ℂ,
        DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} →
        (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N,
          f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) →
        ∃ a : (Fin m → ℤ) → ℂ, (∀ ν, IsCoef X f (T ν) (a ν)) ∧
          ∀ Z ∈ Hn Ψ N, HasSum (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) (f Z) := by sorry
