-- Prove2me | Theorems.Thm_GlobalTheory_SW_Step_hecke_swd
-- name    : GlobalTheory.SW.Step.hecke_swd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:44:25.520561+00:00
-- url     : https://prove2.me/theorems/fa1de2d9-3920-5e4f-814e-0dd81cde6f46
-- title:
--   Step: hecke swd
-- statement:
--   The Step construction uses the hecke swd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilFormulaDegreeSucc.lean#L115-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilFormulaDegreeSucc.lean#L115-L168

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

theorem GlobalTheory.SW.Step.hecke_swd (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M R q : ℕ} {P : Ideal (𝓞 E)}
    {φ : Fam E n N} (h : admitted M R φ) (hP : GoodPrime (R * M) q P) {𝔛 : Lt E N} (h1 : 𝔛.FG)
    (h2 : Agree (R * M) 𝔛 (stdL E N)) :
    ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E),
      A * (q - 1) = q ^ N - 1 ∧
      (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧
        (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧
        ∀ j, ccT (β i j) = β i j) ∧
      ∀ Z ∈ Hn Ψ N, ((q : ℂ) ^ N - 1) * ((q : ℂ) ^ n + (q : ℂ) ^ N) *
          swd Ψ M (twist R 𝔛 φ) Z 0 0 =
        ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, swd Ψ M (twist R (XA i) φ) Z 0 0 +
          ∑ i, ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0) := by sorry
