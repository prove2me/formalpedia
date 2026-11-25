-- Prove2me | Theorems.Thm_GlobalTheory_SW_NbAvg_ncard_carry
-- name    : GlobalTheory.SW.NbAvg.ncard_carry
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:37.846877+00:00
-- url     : https://prove2.me/theorems/1b989146-01f5-4ed7-83c8-0ee424667d7a
-- title:
--   Nb Avg: ncard carry
-- statement:
--   The Nb Avg construction uses the ncard carry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L79-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L79-L113

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

theorem GlobalTheory.SW.NbAvg.ncard_carry {M : ℕ} {P : Ideal (𝓞 E)} {A B : Lt E n} (hN : (Nb M P A).Finite)
    (hB : {h ∈ DH E n M | Moves h B B}.Finite) :
    (carry M P A B).ncard = (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard := by sorry
