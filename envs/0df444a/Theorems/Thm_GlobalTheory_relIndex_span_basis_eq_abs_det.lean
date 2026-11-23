-- Prove2me | Theorems.Thm_GlobalTheory_relIndex_span_basis_eq_abs_det
-- name    : GlobalTheory.relIndex_span_basis_eq_abs_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:43.643009+00:00
-- url     : https://prove2.me/theorems/71a56512-cb12-4ab5-8372-72f7c6036f79
-- title:
--   Global Theory: rel Index span basis eq abs det
-- statement:
--   The Global Theory construction uses the rel Index span basis eq abs det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L79-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable [FiniteDimensional ℚ V]
omit [FiniteDimensional ℚ V]

theorem GlobalTheory.relIndex_span_basis_eq_abs_det {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ V)
    (h : Submodule.span ℤ (Set.range b₁) ≤ Submodule.span ℤ (Set.range b₂)) :
    (((Submodule.span ℤ (Set.range b₁)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range b₂)).toAddSubgroup : ℕ) : ℚ) = |b₂.det b₁| := by sorry
