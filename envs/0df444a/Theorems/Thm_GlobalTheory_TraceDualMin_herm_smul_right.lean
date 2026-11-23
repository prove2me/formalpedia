-- Prove2me | Theorems.Thm_GlobalTheory_TraceDualMin_herm_smul_right
-- name    : GlobalTheory.TraceDualMin.herm_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:16.792327+00:00
-- url     : https://prove2.me/theorems/e8eedab2-1521-4cb8-86b4-270824b9844b
-- title:
--   Trace Dual Min: herm smul right
-- statement:
--   The Trace Dual Min construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean#L21-L23

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

theorem GlobalTheory.TraceDualMin.herm_smul_right {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 x (a • y) = cc a * herm 1 x y := by sorry
