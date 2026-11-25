-- Prove2me | Theorems.Thm_GlobalTheory_spanCovol_comap_subtype
-- name    : GlobalTheory.spanCovol_comap_subtype
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:45.326593+00:00
-- url     : https://prove2.me/theorems/6b7d0397-8513-4b78-9d2c-8b337aa63b1a
-- title:
--   Global Theory: span Covol comap subtype
-- statement:
--   The Global Theory construction uses the span Covol comap subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L153-L157

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

theorem GlobalTheory.spanCovol_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L] (S : Submodule ℝ E)
    (h : (L : Set E) ⊆ S) : spanCovol (ZLattice.comap ℝ L S.subtype) = spanCovol L := by sorry
