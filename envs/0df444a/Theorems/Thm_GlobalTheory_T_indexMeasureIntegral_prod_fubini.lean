-- Prove2me | Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_prod_fubini
-- name    : GlobalTheory.T.indexMeasureIntegral_prod_fubini
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:48.842315+00:00
-- url     : https://prove2.me/theorems/7fce90b8-e845-443a-8507-1a30e1cc7406
-- title:
--   T: index Measure Integral prod fubini
-- statement:
--   The T construction uses the index Measure Integral prod fubini property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralProdFubiniStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralProdFubiniStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubiniStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.indexMeasureIntegral_prod_fubini : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ), Nice (A.prod A') φ → (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧ cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by sorry
