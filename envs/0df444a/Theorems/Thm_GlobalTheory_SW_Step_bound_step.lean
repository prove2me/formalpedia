-- Prove2me | Theorems.Thm_GlobalTheory_SW_Step_bound_step
-- name    : GlobalTheory.SW.Step.bound_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:14.701731+00:00
-- url     : https://prove2.me/theorems/92fe7e4d-97a1-44e7-9600-86b9cf4ad9af
-- title:
--   Step: bound step
-- statement:
--   The Step construction uses the bound step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilFormulaDegreeSucc.lean#L170-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilFormulaDegreeSucc.lean#L170-L236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNbStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistedSiegelWeilDifferenceBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilFormulaDegreeSucc
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Step
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem GlobalTheory.SW.Step.bound_step (hΨ : IsType Ψ) {k : ℕ} (hN0 : 0 < N) (hN : 4 * N < k + k) {M R q : ℕ}
    {P : Ideal (𝓞 E)} {φ : Fam E (k + k) N} (h : admitted M R φ) (hP : GoodPrime (R * M) q P) {S : ℝ}
    (hS : ∀ 𝔛 : Lt E N, 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∀ Z ∈ Hn Ψ N,
      gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤ S)
    (𝔛 : Lt E N) (h1 : 𝔛.FG) (h2 : Agree (R * M) 𝔛 (stdL E N)) (Z : CM Ψ N N)
    (hZ : Z ∈ Hn Ψ N) :
    gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤
      (q : ℝ) ^ k * (1 + (q : ℝ) ^ N) / ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N) * S := by sorry
