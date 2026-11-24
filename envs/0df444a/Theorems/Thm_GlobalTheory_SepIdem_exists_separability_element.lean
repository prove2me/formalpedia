-- Prove2me | Theorems.Thm_GlobalTheory_SepIdem_exists_separability_element
-- name    : GlobalTheory.SepIdem.exists_separability_element
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:53:17.634827+00:00
-- url     : https://prove2.me/theorems/289b5da7-149c-444d-a2a6-3add99efea91
-- title:
--   Sep Idem: exists separability element
-- statement:
--   The Sep Idem construction uses the exists separability element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean#L54-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean#L54-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormallyUnramifiedOfIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.SepIdem

theorem GlobalTheory.SepIdem.exists_separability_element (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [IsReduced O] :
    ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧
      ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0 := by sorry
