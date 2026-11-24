-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_powerSeries_ringHom_extending_finite_free
-- name    : GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:33.649975+00:00
-- url     : https://prove2.me/theorems/3a50d085-527e-4e98-8958-d8570b565792
-- title:
--   T: exists power Series ring Hom extending finite free
-- statement:
--   The T construction uses the exists power Series ring Hom extending finite free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowerSeriesRingHomExtendingFiniteFreeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowerSeriesRingHomExtendingFiniteFreeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowerSeriesRingHomExtendingFiniteFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowerSeriesRingHomExtendingFiniteFreeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free : ∀ (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) → ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = i PowerSeries.X ∧ ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by sorry
