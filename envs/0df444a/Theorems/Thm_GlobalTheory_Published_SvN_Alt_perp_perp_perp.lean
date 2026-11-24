-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_Alt_perp_perp_perp
-- name    : GlobalTheory.Published.SvN.Alt.perp_perp_perp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:56:42.654806+00:00
-- url     : https://prove2.me/theorems/6f59eb91-140c-43e6-9473-5da17315540f
-- title:
--   Alt: perp perp perp
-- statement:
--   The Alt construction uses the perp perp perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L111-L112

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

theorem GlobalTheory.Published.SvN.Alt.perp_perp_perp (h : Alt c) (T : Set W) (a : W) (ha : a ∈ h.perp (h.perp (h.perp T))) : a ∈ h.perp T := by sorry
