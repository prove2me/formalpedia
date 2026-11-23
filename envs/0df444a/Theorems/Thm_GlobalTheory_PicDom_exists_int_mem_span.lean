-- Prove2me | Theorems.Thm_GlobalTheory_PicDom_exists_int_mem_span
-- name    : GlobalTheory.PicDom.exists_int_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:28.383674+00:00
-- url     : https://prove2.me/theorems/f32d77f1-0f4a-4d92-8b66-db9372f88638
-- title:
--   Pic Dom: exists int mem span
-- statement:
--   The Pic Dom construction uses the exists int mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PicDom

theorem GlobalTheory.PicDom.exists_int_mem_span {B : Type} [CommRing B] [IsDomain B] [Algebra.IsIntegral ℤ B] {d : B} (hd : d ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : B) ∈ Ideal.span {d} := by sorry
