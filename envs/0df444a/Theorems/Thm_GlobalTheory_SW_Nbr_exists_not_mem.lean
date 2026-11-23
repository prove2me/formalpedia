-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_exists_not_mem
-- name    : GlobalTheory.SW.Nbr.exists_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:18.284998+00:00
-- url     : https://prove2.me/theorems/37ef2d5f-7b44-44ac-a9d5-149a0b4a1999
-- title:
--   Nbr: exists not mem
-- statement:
--   The Nbr construction uses the exists not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L321-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L321-L332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]

theorem GlobalTheory.SW.Nbr.exists_not_mem {Q : Ideal (𝓞 E)} (hQ : Q ≠ ⊥) {t : E} (ht : ¬ IsIntegral ℤ t)
    (h : ∀ d ∈ Q, IsIntegral ℤ ((d : E) * t)) : ∃ d ∈ Q, ∃ r ∉ Q, ((r : 𝓞 E) : E) = (d : E) * t := by sorry
