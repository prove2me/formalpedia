-- Prove2me | Theorems.Thm_GlobalTheory_Published_SuccMinTransference_of_forall
-- name    : GlobalTheory.Published.SuccMinTransference.of_forall
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:25.576811+00:00
-- url     : https://prove2.me/theorems/c775cc96-6168-43d8-894c-41f7d073ccd2
-- title:
--   Succ Min Transference: of forall
-- statement:
--   The Succ Min Transference construction uses the of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/BesselIntegrals/ExistsLinearIndependentNormLe.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/BesselIntegrals/ExistsLinearIndependentNormLe.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_BesselIntegrals_ExistsLinearIndependentNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory GlobalTheory.Published

theorem GlobalTheory.Published.SuccMinTransference.of_forall
    (h : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (i : ℕ), 1 ≤ i →
      i ≤ finrank ℝ E →
      succMin L i * succMin (dualLattice L) (finrank ℝ E - i + 1) ≤ finrank ℝ E) :
    SuccMinTransference := by sorry
