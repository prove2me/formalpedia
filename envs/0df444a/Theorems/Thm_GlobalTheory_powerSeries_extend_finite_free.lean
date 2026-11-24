-- Prove2me | Theorems.Thm_GlobalTheory_powerSeries_extend_finite_free
-- name    : GlobalTheory.powerSeries_extend_finite_free
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:20.818302+00:00
-- url     : https://prove2.me/theorems/f068947a-a044-4f7a-bbdc-f0735b6127cd
-- title:
--   Global Theory: power Series extend finite free
-- statement:
--   The Global Theory construction uses the power Series extend finite free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowerSeriesRingHomExtendingFiniteFree.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowerSeriesRingHomExtendingFiniteFree.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompCMulMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowerSeriesRingHomExtendingFiniteFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.powerSeries_extend_finite_free (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K]
    [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K)
    (io : O₁ →+* K) (h : ∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧
      Φ PowerSeries.X = i PowerSeries.X ∧
      ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by sorry
