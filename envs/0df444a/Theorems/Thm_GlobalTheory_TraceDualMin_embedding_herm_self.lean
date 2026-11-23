-- Prove2me | Theorems.Thm_GlobalTheory_TraceDualMin_embedding_herm_self
-- name    : GlobalTheory.TraceDualMin.embedding_herm_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:45.664037+00:00
-- url     : https://prove2.me/theorems/161d550d-d773-44fc-bf6f-158d23763f38
-- title:
--   Trace Dual Min: embedding herm self
-- statement:
--   The Trace Dual Min construction uses the embedding herm self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean#L37-L39

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

theorem GlobalTheory.TraceDualMin.embedding_herm_self {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) :
    σ (herm 1 x x) = ((∑ k, ‖σ (x k)‖ ^ 2 : ℝ) : ℂ) := by sorry
