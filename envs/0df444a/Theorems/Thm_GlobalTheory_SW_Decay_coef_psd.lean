-- Prove2me | Theorems.Thm_GlobalTheory_SW_Decay_coef_psd
-- name    : GlobalTheory.SW.Decay.coef_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:43.266516+00:00
-- url     : https://prove2.me/theorems/1ff55687-75e1-4887-a710-0f5fe9f3f2a0
-- title:
--   Decay: coef psd
-- statement:
--   The Decay construction uses the coef psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCusps.lean#L120-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCusps.lean#L120-L151

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
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}

theorem GlobalTheory.SW.Decay.coef_psd (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) (h0 : a ≠ 0) (τ : Ψ) :
    (T.map τ.1).PosSemidef := by sorry
