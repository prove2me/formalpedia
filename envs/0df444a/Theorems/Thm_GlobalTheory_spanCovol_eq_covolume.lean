-- Prove2me | Theorems.Thm_GlobalTheory_spanCovol_eq_covolume
-- name    : GlobalTheory.spanCovol_eq_covolume
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:45.503948+00:00
-- url     : https://prove2.me/theorems/3a1e530a-6bba-4339-8c99-661c7bcc3265
-- title:
--   Global Theory: span Covol eq covolume
-- statement:
--   The Global Theory construction uses the span Covol eq covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L141-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem GlobalTheory.spanCovol_eq_covolume [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : spanCovol L = ZLattice.covolume L := by sorry
