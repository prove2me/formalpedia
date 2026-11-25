-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_summable_norm_mul_one_add_pow
-- name    : GlobalTheory.schwartz_summable_norm_mul_one_add_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:46.924893+00:00
-- url     : https://prove2.me/theorems/ccefb599-ba78-4ba1-8c6d-069d452dbd79
-- title:
--   Global Theory: schwartz summable norm mul one add pow
-- statement:
--   The Global Theory construction uses the schwartz summable norm mul one add pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeDualFourierExpansionSchwartz.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeDualFourierExpansionSchwartz.lean#L9-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap
open GlobalTheory

theorem GlobalTheory.schwartz_summable_norm_mul_one_add_pow {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (h : 𝓢(V, ℂ)) (N : ℕ) : Summable fun l : Λ => ‖h l‖ * (1 + ‖(l : V)‖) ^ N := by sorry
