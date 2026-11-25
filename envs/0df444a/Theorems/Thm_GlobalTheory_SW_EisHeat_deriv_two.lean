-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisHeat_deriv_two
-- name    : GlobalTheory.SW.EisHeat.deriv_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:00:55.347714+00:00
-- url     : https://prove2.me/theorems/cb0e6e60-4334-5036-b73d-9811e69885b7
-- title:
--   Eis Heat: deriv two
-- statement:
--   The Eis Heat construction uses the deriv two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisensteinSeriesOfSchwartzIsHolomorphic.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisensteinSeriesOfSchwartzIsHolomorphic.lean#L29-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisHeat
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]

theorem GlobalTheory.SW.EisHeat.deriv_two {f : X → ℂ} {U : Set X} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {p : X}
    (hp : p ∈ U) (v w : X) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) 0 =
      fderiv ℂ (fderiv ℂ f) p v w := by sorry
