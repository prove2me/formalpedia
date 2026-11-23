-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_Alt_sq_swap
-- name    : GlobalTheory.Published.SvN.Alt.sq_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:41.881009+00:00
-- url     : https://prove2.me/theorems/2bc5e1ca-ad9f-48ad-8e27-a04183c16368
-- title:
--   Alt: sq swap
-- statement:
--   The Alt construction uses the sq swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L99-L101

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
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}

theorem GlobalTheory.Published.SvN.Alt.sq_swap (h : Alt c) {x y : W} (hxy : c x y ^ 2 = 1) : c y x ^ 2 = 1 := by sorry
