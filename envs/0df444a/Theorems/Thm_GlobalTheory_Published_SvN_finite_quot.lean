-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_finite_quot
-- name    : GlobalTheory.Published.SvN.finite_quot
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:07.010205+00:00
-- url     : https://prove2.me/theorems/de66a9e1-4261-4edd-ab65-4b108cda203e
-- title:
--   Sv N: finite quot
-- statement:
--   The Sv N construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L368-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L368-L378

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN

theorem GlobalTheory.Published.SvN.finite_quot {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] (A U : AddSubgroup W)
    (hU : (U : Set W) ∈ 𝓝 0) {K : Set W} (hK : IsCompact K) (hA : (A : Set W) ⊆ K) : Finite (A ⧸ U.addSubgroupOf A) := by sorry
