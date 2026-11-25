-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisHeat_isHeat_tsum
-- name    : GlobalTheory.SW.EisHeat.isHeat_tsum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:32.495141+00:00
-- url     : https://prove2.me/theorems/f78172e5-0c85-4537-a328-0f75b2d4445e
-- title:
--   Eis Heat: is Heat tsum
-- statement:
--   The Eis Heat construction uses the is Heat tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisensteinSeriesOfSchwartzIsHolomorphic.lean#L123-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisensteinSeriesOfSchwartzIsHolomorphic.lean#L123-L145

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
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem GlobalTheory.SW.EisHeat.isHeat_tsum {ι : Type} {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i))
    (hle : ∀ p : CF Ψ N N × CF Ψ n N × CF Ψ n N, (p.1 : CM Ψ N N) ∈ Hn Ψ N → ∃ t ∈ 𝓝 p,
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ q ∈ t, ‖D i q.1 q.2.1 q.2.2‖ ≤ u i) :
    IsHeat Ψ fun Z z z' => ∑' i, D i Z z z' := by sorry
