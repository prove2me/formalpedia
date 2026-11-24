-- Prove2me | Theorems.Thm_GlobalTheory_SW_NbAvg_sum_nb
-- name    : GlobalTheory.SW.NbAvg.sum_nb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:56.684128+00:00
-- url     : https://prove2.me/theorems/b11ffe5f-8967-4c4d-94a3-e62f167a2541
-- title:
--   Nb Avg: sum nb
-- statement:
--   The Nb Avg construction uses the sum nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L188-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L188-L223

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

theorem GlobalTheory.SW.NbAvg.sum_nb {M : ℕ} [Fintype (Cls E n M)] {P : Ideal (𝓞 E)} {A : Lt E n}
    (hN : (Nb M P A).Finite) {f : Lt E n → ℂ} (hf : IsClassFn M f) :
    ∑ᶠ X ∈ Nb M P A, f X =
      ∑ c : Cls E n M, ((nbIn M P A (Quot.out c).1).ncard : ℂ) * f (Quot.out c).1 := by sorry
