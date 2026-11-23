-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_index_iff
-- name    : GlobalTheory.SW.Nbr.index_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:13.470022+00:00
-- url     : https://prove2.me/theorems/f4d42131-6744-4231-a386-5647b14c23bb
-- title:
--   Nbr: index iff
-- statement:
--   The Nbr construction uses the index iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L243-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L243-L256

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

theorem GlobalTheory.SW.Nbr.index_iff {q : ℕ} {P : Ideal (𝓞 E)} (hq : q.Prime) (hP : Ideal.absNorm P = q)
    {Λ : Lt E n} (N : Submodule (𝓞 E) Λ) :
    ((∀ c ∈ P, ∀ x, c • x ∈ N) ∧ N.toAddSubgroup.index = q) ↔
      ∃ f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by sorry
