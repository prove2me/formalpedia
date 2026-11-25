-- Prove2me | Theorems.Thm_GlobalTheory_SW_NbAvg_wt_mul_nbIn
-- name    : GlobalTheory.SW.NbAvg.wt_mul_nbIn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:56.758687+00:00
-- url     : https://prove2.me/theorems/e7262fa5-da71-43da-aa9a-f59ac9504faa
-- title:
--   Nb Avg: wt mul nb In
-- statement:
--   The Nb Avg construction uses the wt mul nb In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L150-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L150-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
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
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.SW.NbAvg.wt_mul_nbIn {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) :
    (wt M A : ℂ) * (nbIn M P A B).ncard = (wt M B : ℂ) * (nbIn M (conjI P) B A).ncard := by sorry
