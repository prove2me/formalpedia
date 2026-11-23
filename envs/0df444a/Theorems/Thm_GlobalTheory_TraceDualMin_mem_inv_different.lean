-- Prove2me | Theorems.Thm_GlobalTheory_TraceDualMin_mem_inv_different
-- name    : GlobalTheory.TraceDualMin.mem_inv_different
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:04.312141+00:00
-- url     : https://prove2.me/theorems/fd1e9e6e-6ff3-4089-8612-26beea155829
-- title:
--   Trace Dual Min: mem inv different
-- statement:
--   The Trace Dual Min construction uses the mem inv different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean#L43-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.TraceDualMin
omit [IsCMField E]

theorem GlobalTheory.TraceDualMin.mem_inv_different {x : E} (hx : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k) :
    x ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by sorry
