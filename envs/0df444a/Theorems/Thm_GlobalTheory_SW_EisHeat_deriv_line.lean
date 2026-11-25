-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisHeat_deriv_line
-- name    : GlobalTheory.SW.EisHeat.deriv_line
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:57.276393+00:00
-- url     : https://prove2.me/theorems/de5132d0-8ee5-4902-9845-64fe133c1669
-- title:
--   Eis Heat: deriv line
-- statement:
--   The Eis Heat construction uses the deriv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisensteinSeriesOfSchwartzIsHolomorphic.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisensteinSeriesOfSchwartzIsHolomorphic.lean#L22-L27

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
omit [FiniteDimensional ℂ X]

theorem GlobalTheory.SW.EisHeat.deriv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : X → V} {p : X}
    (hf : DifferentiableAt ℂ f p) (v : X) :
    HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ f p v) 0 := by sorry
